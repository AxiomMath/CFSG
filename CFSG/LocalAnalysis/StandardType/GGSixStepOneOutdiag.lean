module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section Inndiag

variable (R : Type) [Group R] (I : Set (MulAut R))

@[expose] def ggInndiag : Subgroup (MulAut R) :=
  (MulAut.conj : R →* MulAut R).range ⊔ Subgroup.closure I

@[expose] def GGInndiagNormal : Prop :=
  ∀ α : MulAut R, ∀ φ ∈ I, α * φ * α⁻¹ ∈ ggInndiag R I

variable {R I}

theorem inn_le_ggInndiag : (MulAut.conj : R →* MulAut R).range ≤ ggInndiag R I := le_sup_left

theorem subset_ggInndiag : I ⊆ ggInndiag R I := fun _ h =>
  Subgroup.mem_sup_right (Subgroup.subset_closure h)

theorem ggMulAut_conj_inn_outdiag (α : MulAut R) (r : R) :
    α * MulAut.conj r * α⁻¹ = MulAut.conj (α r) := by
  ext s
  simp [MulAut.conj_apply]

theorem ggInndiagNormal_of_subset_inn (h : I ⊆ (MulAut.conj : R →* MulAut R).range) :
    GGInndiagNormal R I := by
  intro α φ hφ
  obtain ⟨r, rfl⟩ := h hφ
  rw [ggMulAut_conj_inn_outdiag]
  exact inn_le_ggInndiag ⟨α r, rfl⟩

theorem GGInndiagNormal.conj_mem (h : GGInndiagNormal R I) (α : MulAut R) {φ : MulAut R}
    (hφ : φ ∈ ggInndiag R I) : α * φ * α⁻¹ ∈ ggInndiag R I := by
  have hle : ggInndiag R I ≤ (ggInndiag R I).comap (MulAut.conj α).toMonoidHom := by
    refine sup_le ?_ ?_
    · rintro _ ⟨r, rfl⟩
      show (MulAut.conj α) (MulAut.conj r) ∈ ggInndiag R I
      rw [MulAut.conj_apply, ggMulAut_conj_inn_outdiag]
      exact inn_le_ggInndiag ⟨α r, rfl⟩
    · rw [Subgroup.closure_le]
      intro ψ hψ
      show (MulAut.conj α) ψ ∈ ggInndiag R I
      rw [MulAut.conj_apply]
      exact h α ψ hψ
  have := hle hφ
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem GGOutdiagCyclic.exists_le (h : GGOutdiagCyclic R I) :
    ∃ φ₀ : MulAut R,
      ggInndiag R I ≤ (MulAut.conj : R →* MulAut R).range ⊔ Subgroup.zpowers φ₀ := by
  obtain ⟨φ₀, hφ₀⟩ := h
  exact ⟨φ₀, sup_le le_sup_left (Subgroup.closure_le _ |>.mpr hφ₀)⟩

theorem GGOutdiagCyclic.isCyclic_map (h : GGOutdiagCyclic R I) :
    IsCyclic ((ggInndiag R I).map
      (QuotientGroup.mk' (MulAut.conj : R →* MulAut R).range)) := by
  obtain ⟨φ₀, hle⟩ := h.exists_le
  exact Subgroup.isCyclic_of_le ((Subgroup.map_mono hle).trans (map_sup_zpowers_le _ φ₀))

theorem GGOutdiagCyclic.commutator_mem (h : GGOutdiagCyclic R I) {a b : MulAut R}
    (ha : a ∈ ggInndiag R I) (hb : b ∈ ggInndiag R I) :
    ⁅a, b⁆ ∈ (MulAut.conj : R →* MulAut R).range := by
  set N := (MulAut.conj : R →* MulAut R).range with hN
  have := h.isCyclic_map
  have hc : IsMulCommutative ((ggInndiag R I).map (QuotientGroup.mk' N)) := inferInstance
  have hcomm := hc.is_comm.comm
    ⟨QuotientGroup.mk' N a, a, ha, rfl⟩ ⟨QuotientGroup.mk' N b, b, hb, rfl⟩
  have hcomm' : QuotientGroup.mk' N a * QuotientGroup.mk' N b =
      QuotientGroup.mk' N b * QuotientGroup.mk' N a := congrArg Subtype.val hcomm
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact hcomm'

end Inndiag

section Induced

variable {G : Type} [Group G] (K : Subgroup G) {R : Type} [Group R]
  (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R))

theorem ggLAut_of_mem_outdiag {k : G} (hk : k ∈ K) :
    ggLAut K θ ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (θ ((⟨k, hk⟩ : K) : K ⧸ Subgroup.center K)) := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [ggLAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2

theorem ggLAut_of_mem_centralizer_outdiag {c : G} (hc : c ∈ Subgroup.centralizer (K : Set G)) :
    ggLAut K θ ⟨c, Subgroup.centralizer_le_normalizer (K : Set G) hc⟩ = 1 :=
  ggLAut_eq_one_of_mem_centralizer K θ hc

theorem mem_sup_centralizer_of_ggLAut_mem (hK : commutator K = ⊤)
    {g : Subgroup.normalizer (K : Set G)}
    (h : ggLAut K θ g ∈ (MulAut.conj : R →* MulAut R).range) :
    (g : G) ∈ K ⊔ Subgroup.centralizer (K : Set G) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H k =>
    set k' : Subgroup.normalizer (K : Set G) := ⟨(k : G), Subgroup.le_normalizer k.2⟩ with hk'
    have hk'aut : ggLAut K θ k' = MulAut.conj (θ (k : K ⧸ Subgroup.center K)) :=
      ggLAut_of_mem_outdiag K θ k.2
    have h1 : ggLAut K θ (g * k'⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hr, hk'aut, mul_inv_cancel]
    have hc := mem_centralizer_of_ggLAut_eq_one K θ hK h1
    have hg : (g : G) = ((g * k'⁻¹ : Subgroup.normalizer (K : Set G)) : G) * (k : G) := by
      simp [hk']
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left k.2)

@[expose] noncomputable def ggInndiagPre : Subgroup G :=
  ((ggInndiag R I).comap (ggLAut K θ)).map (Subgroup.normalizer (K : Set G)).subtype

variable {K θ I}

theorem mem_ggInndiagPre_iff {g : G} : g ∈ ggInndiagPre K θ I ↔
    ∃ hg : g ∈ Subgroup.normalizer (K : Set G), ggLAut K θ ⟨g, hg⟩ ∈ ggInndiag R I := by
  constructor
  · rintro ⟨⟨g', hg'⟩, h, rfl⟩
    exact ⟨hg', h⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem ggInndiagPre_le_normalizer :
    ggInndiagPre K θ I ≤ Subgroup.normalizer (K : Set G) := fun _ hg =>
  (mem_ggInndiagPre_iff.mp hg).1

variable (K θ I) in
theorem sup_centralizer_le_ggInndiagPre :
    K ⊔ Subgroup.centralizer (K : Set G) ≤ ggInndiagPre K θ I := by
  refine sup_le (fun k hk => mem_ggInndiagPre_iff.mpr ⟨Subgroup.le_normalizer hk, ?_⟩)
    (fun c hc => mem_ggInndiagPre_iff.mpr ⟨Subgroup.centralizer_le_normalizer (K : Set G) hc, ?_⟩)
  · rw [ggLAut_of_mem_outdiag K θ hk]
    exact inn_le_ggInndiag ⟨_, rfl⟩
  · rw [ggLAut_of_mem_centralizer_outdiag K θ hc]
    exact one_mem _

theorem le_ggInndiagPre_of_induces {S : Subgroup G} (hSN : S ≤ Subgroup.normalizer (K : Set G))
    (hS : ∀ s ∈ S, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = s⁻¹ * l * s) φ) :
    S ≤ ggInndiagPre K θ I := fun _ hs =>
  mem_ggInndiagPre_iff.mpr ⟨hSN hs, subset_ggInndiag (ggLAut_mem_of_induces K θ hSN hS hs)⟩

theorem conj_mem_ggInndiagPre (hN : GGInndiagNormal R I) {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) {g : G} (hg : g ∈ ggInndiagPre K θ I) :
    n * g * n⁻¹ ∈ ggInndiagPre K θ I := by
  obtain ⟨hgN, hgI⟩ := mem_ggInndiagPre_iff.mp hg
  refine mem_ggInndiagPre_iff.mpr ⟨mul_mem (mul_mem hn hgN) (inv_mem hn), ?_⟩
  have h := hN.conj_mem (ggLAut K θ ⟨n, hn⟩) hgI
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact h

theorem commutator_ggInndiagPre_le (hK : commutator K = ⊤) (hO : GGOutdiagCyclic R I) :
    ⁅ggInndiagPre K θ I, ggInndiagPre K θ I⁆ ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨haN, haI⟩ := mem_ggInndiagPre_iff.mp ha
  obtain ⟨hbN, hbI⟩ := mem_ggInndiagPre_iff.mp hb
  have hc := hO.commutator_mem haI hbI
  rw [← map_commutatorElement] at hc
  exact mem_sup_centralizer_of_ggLAut_mem K θ hK hc

end Induced

section Main

variable {G : Type} [Group G] {K : Subgroup G} {R : Type} [Group R]
  {θ : K ⧸ Subgroup.center K ≃* R} {I : Set (MulAut R)}

theorem le_sup_centralizer_of_inndiag (hK : commutator K = ⊤) (hO : GGOutdiagCyclic R I)
    (hN : GGInndiagNormal R I) {D X : Subgroup G} (hD : D ≤ ggInndiagPre K θ I)
    (hX : X ≤ Subgroup.normalizer (K : Set G)) (hXD : ⁅X, D⁆ = X) :
    X ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
  have hXW : X ≤ ggInndiagPre K θ I := by
    rw [← hXD, Subgroup.commutator_le]
    intro a ha d hd
    rw [commutatorElement_def]
    exact mul_mem (conj_mem_ggInndiagPre hN (hX ha) (hD hd)) (inv_mem (hD hd))
  calc X = ⁅X, D⁆ := hXD.symm
    _ ≤ ⁅ggInndiagPre K θ I, ggInndiagPre K θ I⁆ := Subgroup.commutator_mono hXW hD
    _ ≤ K ⊔ Subgroup.centralizer (K : Set G) := commutator_ggInndiagPre_le hK hO

omit [Group R] in
theorem ggConj_mem_centralizer_of_mem_normalizer {n c : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) (hc : c ∈ Subgroup.centralizer (K : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro k hk
  have hk' : n⁻¹ * k * n⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) k).mp hk
  have h := hc _ hk'
  rw [inv_inv] at h
  calc k * (n * c * n⁻¹) = n * ((n⁻¹ * k * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * k * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * k := by group

theorem exists_zpow_ggLAut_mem_inn (hO : GGOutdiagCyclic R I) (hN : GGInndiagNormal R I)
    (n : Subgroup.normalizer (K : Set G)) :
    ∃ m : ℤ, ∀ s : Subgroup.normalizer (K : Set G), ggLAut K θ s ∈ ggInndiag R I →
      ggLAut K θ (n * s * n⁻¹ * (s ^ m)⁻¹) ∈ (MulAut.conj : R →* MulAut R).range := by
  set Nn := (MulAut.conj : R →* MulAut R).range with hNn
  have hcyc : IsCyclic ((ggInndiag R I).map (QuotientGroup.mk' Nn)) := hO.isCyclic_map
  set a : MulAut R ⧸ Nn := QuotientGroup.mk' Nn (ggLAut K θ n) with ha
  have hpres : ∀ y ∈ (ggInndiag R I).map (QuotientGroup.mk' Nn),
      a * y * a⁻¹ ∈ (ggInndiag R I).map (QuotientGroup.mk' Nn) := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨ggLAut K θ n * φ * (ggLAut K θ n)⁻¹, hN.conj_mem _ hφ, ?_⟩
    rw [ha, map_mul, map_mul, map_inv]
  let σ : (ggInndiag R I).map (QuotientGroup.mk' Nn) →*
      (ggInndiag R I).map (QuotientGroup.mk' Nn) :=
    { toFun := fun y => ⟨a * y * a⁻¹, hpres y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y z => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ
  refine ⟨m, fun s hs => ?_⟩
  have h1 : a * QuotientGroup.mk' Nn (ggLAut K θ s) * a⁻¹ =
      QuotientGroup.mk' Nn (ggLAut K θ s) ^ m :=
    congrArg Subtype.val (hm ⟨QuotientGroup.mk' Nn (ggLAut K θ s), ggLAut K θ s, hs, rfl⟩)
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
  simp only [map_mul, map_inv, map_zpow]
  rw [← ha, h1, mul_inv_cancel]

theorem normalizer_le_normalizer_sup_of_inndiag (hK : commutator K = ⊤)
    (hO : GGOutdiagCyclic R I) (hN : GGInndiagNormal R I) {S : Subgroup G}
    (hS : S ≤ ggInndiagPre K θ I) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((S ⊔ K ⊔ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
  have key : ∀ n ∈ Subgroup.normalizer (K : Set G), ∀ s ∈ S,
      n * s * n⁻¹ ∈ S ⊔ (K ⊔ Subgroup.centralizer (K : Set G)) := by
    intro n hn s hs
    obtain ⟨hsN, hsI⟩ := mem_ggInndiagPre_iff.mp (hS hs)
    obtain ⟨m, hm⟩ := exists_zpow_ggLAut_mem_inn (θ := θ) hO hN ⟨n, hn⟩
    have h3 := mem_sup_centralizer_of_ggLAut_mem K θ hK (hm ⟨s, hsN⟩ hsI)
    have hg : n * s * n⁻¹ =
        ((⟨n, hn⟩ * ⟨s, hsN⟩ * ⟨n, hn⟩⁻¹ * (⟨s, hsN⟩ ^ m)⁻¹ : Subgroup.normalizer (K : Set G)) :
          G) * s ^ m := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      group
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h3) (Subgroup.mem_sup_left (zpow_mem hs m))
  have hmap : ∀ n ∈ Subgroup.normalizer (K : Set G),
      ∀ h ∈ S ⊔ (K ⊔ Subgroup.centralizer (K : Set G)),
        n * h * n⁻¹ ∈ S ⊔ (K ⊔ Subgroup.centralizer (K : Set G)) := by
    intro n hn h hh
    have hle : S ⊔ (K ⊔ Subgroup.centralizer (K : Set G)) ≤
        (S ⊔ (K ⊔ Subgroup.centralizer (K : Set G))).comap (MulAut.conj n).toMonoidHom := by
      refine sup_le (fun s hs => ?_) (sup_le (fun k hk => ?_) (fun c hc => ?_)) <;>
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      · exact key n hn s hs
      · exact Subgroup.mem_sup_right
          (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hn k).mp hk))
      · exact Subgroup.mem_sup_right
          (Subgroup.mem_sup_right (ggConj_mem_centralizer_of_mem_normalizer hn hc))
    have := hle hh
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  intro n hn
  rw [sup_assoc, Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hmap n hn h hh, fun hh => ?_⟩
  have := hmap n⁻¹ (inv_mem hn) _ hh
  have e : n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h := by group
  rwa [e] at this

end Main

end CFSG.StandardType
