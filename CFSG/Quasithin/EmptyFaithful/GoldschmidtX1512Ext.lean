module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Mod

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace X1512

variable {G : Type} [Group G] {n : ℕ} {L X : Subgroup G} [(L.subgroupOf X).Normal]
  {β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X}

@[expose] def Realizes (β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X) (k : G)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ (u : ↥(G6.coreMod n)) (x : ↥X), β u = QuotientGroup.mk x →
    ∃ hkx : k * (x : G) * k⁻¹ ∈ X, β (G6.coreAct n σ u) = QuotientGroup.mk ⟨k * x * k⁻¹, hkx⟩

theorem realizes_one : Realizes β 1 1 := fun u x hu => by
  refine ⟨by simp, ?_⟩
  rw [map_one, MulAut.one_apply, hu]
  exact congrArg QuotientGroup.mk (Subtype.ext (by simp))

theorem Realizes.mul {k k' : G} {σ σ' : Equiv.Perm (Fin n)} (h : Realizes β k σ)
    (h' : Realizes β k' σ') : Realizes β (k * k') (σ * σ') := by
  intro u x hu
  obtain ⟨hx', e'⟩ := h' u x hu
  obtain ⟨hx, e⟩ := h _ _ e'
  have hmem : k * k' * (x : G) * (k * k')⁻¹ ∈ X := by
    have : k * k' * (x : G) * (k * k')⁻¹ = k * (k' * x * k'⁻¹) * k⁻¹ := by group
    rwa [this]
  refine ⟨hmem, ?_⟩
  rw [map_mul, MulAut.mul_apply, e]
  exact congrArg QuotientGroup.mk (Subtype.ext (by simp only [mul_assoc, mul_inv_rev]))

theorem Realizes.unique (hn : n = 3 ∨ n = 5) (hi : Function.Injective β) {k : G}
    {σ σ' : Equiv.Perm (Fin n)} (h : Realizes β k σ) (h' : Realizes β k σ') : σ = σ' := by
  apply coreAct_injective hn
  apply MulEquiv.ext
  intro u
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β u)
  obtain ⟨_, e1⟩ := h u x hx.symm
  obtain ⟨_, e2⟩ := h' u x hx.symm
  exact hi (e1.trans e2.symm)

theorem NatMod.realizes {K : Subgroup G} {Ψ : ↥K →* Equiv.Perm (Fin n)}
    (hM : NatMod n K L X Ψ β) (k : ↥K) : Realizes β (k : G) (Ψ k) := hM.equiv k

variable {K : Subgroup G} {Ψ : ↥K →* Equiv.Perm (Fin n)}

theorem NatMod.ψ_eq_one_iff (hn : n = 3 ∨ n = 5) (hM : NatMod n K L X Ψ β) (hLX : L ≤ X)
    (k : ↥K) : Ψ k = 1 ↔ ∀ x ∈ X, (k : G) * x * (k : G)⁻¹ * x⁻¹ ∈ L := by
  constructor
  · intro h x hx
    obtain ⟨u, hu⟩ := hM.surj (QuotientGroup.mk ⟨x, hx⟩)
    obtain ⟨hkx, e⟩ := hM.equiv k u ⟨x, hx⟩ hu
    rw [h, map_one, MulAut.one_apply, hu] at e
    exact (mk_eq_iff hLX).mp e
  · intro h
    refine Realizes.unique hn hM.inj (hM.realizes k) ?_
    intro u x hu
    have hkx : (k : G) * (x : G) * (k : G)⁻¹ ∈ X := by
      have := h x x.2
      have e : (k : G) * (x : G) * (k : G)⁻¹ = ((k : G) * x * (k : G)⁻¹ * (x : G)⁻¹) * x := by
        group
      rw [e]
      exact X.mul_mem (hLX this) x.2
    refine ⟨hkx, ?_⟩
    rw [map_one, MulAut.one_apply, hu]
    exact (mk_eq_iff hLX).mpr (by simpa using h x x.2)

theorem exists_natMod_ext (hn : n = 3 ∨ n = 5) {F : Subgroup G} (hLX : L ≤ X) (hFK : F ≤ K)
    (hF : NaturalSn n F L X) (hKX : ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ ∈ X)
    (hact : ∀ k ∈ K, ∃ f ∈ F, ∀ x ∈ X, k * x * k⁻¹ * (f * x * f⁻¹)⁻¹ ∈ L) :
    ∃ (θ : ↥F →* Equiv.Perm (Fin n)) (Ψ : ↥K →* Equiv.Perm (Fin n))
      (β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X),
      Function.Surjective θ ∧ θ.ker = (cSecIn F L X).subgroupOf F ∧
      NatMod n F L X θ β ∧ NatMod n K L X Ψ β ∧
      ∀ (f : G) (hf : f ∈ F), Ψ ⟨f, hFK hf⟩ = θ ⟨f, hf⟩ := by
  obtain ⟨θ, β, hθs, hθk, hβs, hβk, hequiv⟩ := hF
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, natKer_eq_bot hn]
  have hex : ∀ k : ↥K, ∃ σ, Realizes β (k : G) σ := fun k => by
    obtain ⟨f, hf, h⟩ := hact k k.2
    refine ⟨θ ⟨f, hf⟩, fun u x hu => ?_⟩
    obtain ⟨hfx, e⟩ := hequiv ⟨f, hf⟩ u x hu
    refine ⟨hKX k k.2 x x.2, ?_⟩
    rw [e]
    exact (mk_eq_iff hLX).mpr (h x x.2)
  choose ψ hψ using hex
  let Ψ : ↥K →* Equiv.Perm (Fin n) :=
    { toFun := ψ
      map_one' := Realizes.unique hn hβi (hψ 1) (by simpa using (realizes_one (β := β)))
      map_mul' := fun a b => Realizes.unique hn hβi (hψ (a * b)) (by
        simpa using (hψ a).mul (hψ b)) }
  refine ⟨θ, Ψ, β, hθs, hθk, ⟨hβs, hβi, hequiv⟩, ⟨hβs, hβi, fun k u x hu => hψ k u x hu⟩, ?_⟩
  intro f hf
  exact Realizes.unique hn hβi (hψ ⟨f, hFK hf⟩) (fun u x hu => hequiv ⟨f, hf⟩ u x hu)

theorem NatMod.irreducible (hn : n = 3 ∨ n = 5) {F : Subgroup G} {θ : ↥F →* Equiv.Perm (Fin n)}
    (hθs : Function.Surjective θ) (hM : NatMod n F L X θ β) (hLX : L ≤ X) {Y : Subgroup G}
    (hLY : L ≤ Y) (hYX : Y ≤ X) (hY : ∀ f ∈ F, ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) : Y = L ∨ Y = X := by
  let W : Subgroup ↥(G6.coreMod n) :=
    ((Y.subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X))).comap β
  have hmemW : ∀ u, u ∈ W ↔ ∃ y : ↥X, (y : G) ∈ Y ∧ QuotientGroup.mk y = β u := by
    intro u
    constructor
    · rintro ⟨y, hy, hyu⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hyu⟩
    · rintro ⟨y, hy, hyu⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, hyu⟩
  have hinv : ∀ σ : Equiv.Perm (Fin n), ∀ u ∈ W, G6.coreAct n σ u ∈ W := by
    intro σ u hu
    obtain ⟨f, rfl⟩ := hθs σ
    obtain ⟨y, hyY, hyu⟩ := (hmemW u).mp hu
    obtain ⟨hfy, e⟩ := hM.equiv f u y hyu.symm
    exact (hmemW _).mpr ⟨⟨f * y * f⁻¹, hfy⟩, hY f f.2 y hyY, e.symm⟩
  rcases coreMod_irreducible hn W hinv with h | h
  · left
    refine le_antisymm (fun y hy => ?_) hLY
    obtain ⟨u, hu⟩ := hM.surj (QuotientGroup.mk ⟨y, hYX hy⟩)
    have huW : u ∈ W := (hmemW u).mpr ⟨⟨y, hYX hy⟩, hy, hu.symm⟩
    rw [h, Subgroup.mem_bot] at huW
    rw [huW, map_one] at hu
    have := (QuotientGroup.eq_one_iff _).mp hu.symm
    exact Subgroup.mem_subgroupOf.mp this
  · right
    refine le_antisymm hYX (fun x hx => ?_)
    obtain ⟨u, hu⟩ := hM.surj (QuotientGroup.mk ⟨x, hx⟩)
    have huW : u ∈ W := by rw [h]; exact Subgroup.mem_top u
    obtain ⟨y, hyY, hyu⟩ := (hmemW u).mp huW
    have h1 := (mk_eq_iff hLX).mp (hyu.trans hu)
    have e : x = (x * (y : G)⁻¹) * y := by group
    rw [e]
    exact Y.mul_mem (hLY h1) hyY

end X1512

end CFSG.Quasithin
