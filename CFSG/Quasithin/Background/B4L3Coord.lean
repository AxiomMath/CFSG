module

public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

variable {V : Type*} [CommGroup V]

structure L3Data (G : Subgroup (MulAut V)) (U Z : Subgroup V) where
  π : L3.Γ →* ↥G
  β : ↥U →* Multiplicative L3.Vec
  π_surj : Function.Surjective π
  β_surj : Function.Surjective β
  ker_β : ∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z
  Z_le : Z ≤ U
  inv_U : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U
  inv_Z : ∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z
  equi : ∀ (γ : L3.Γ) (u : ↥U) (hu : ((π γ : ↥G) : MulAut V) (u : V) ∈ U),
    β ⟨((π γ : ↥G) : MulAut V) (u : V), hu⟩ =
      Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd (β u)))

@[expose] def L3Coord (G : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  Nonempty (L3Data G U Z)

theorem FFModel.RealizesVia.coord {D : FFModel} (hs : D.sec = ⊤) (hk : D.ker = ⊥)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    ∃ β : ↥U →* D.Amb, Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : D.Gam) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = D.act γ (β u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  let κ : (↥D.sec ⧸ D.ker.subgroupOf D.sec) →* D.Amb :=
    QuotientGroup.lift (D.ker.subgroupOf D.sec) D.sec.subtype (by
      intro x hx
      have h1 : (x : D.Amb) ∈ D.ker := Subgroup.mem_subgroupOf.mp hx
      rw [hk, Subgroup.mem_bot] at h1
      exact h1)
  have hκinj : ∀ x : (↥D.sec ⧸ D.ker.subgroupOf D.sec), κ x = 1 → x = 1 := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H m =>
      have h1 : (m : D.Amb) = 1 := hx
      have : m = 1 := Subtype.ext h1
      rw [this]
      rfl
  have hall : ∀ x : D.Amb, x ∈ D.sec := fun x => by rw [hs]; exact Subgroup.mem_top x
  refine ⟨κ.comp β, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hall m⟩)
    refine ⟨u, ?_⟩
    show κ (β u) = m
    rw [hu]
    exact QuotientGroup.lift_mk _ _ _
  · intro u
    rw [← hβk u]
    constructor
    · intro h1
      exact hκinj _ h1
    · intro h1
      show κ (β u) = 1
      rw [h1]
      exact map_one κ
  · intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hm' : D.act γ (m : D.Amb) ∈ D.sec := hall _
    have h1 := hβe γ u m hu hm' hm.symm
    show κ (β ⟨_, hu⟩) = D.act γ (κ (β u))
    rw [h1, ← hm]
    rfl

theorem BinaryNaturalSL.toL3Coord {G : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : BinaryNaturalSL G U Z 3 1) : L3Coord G U Z := by
  obtain ⟨K, hF, hfin, hcard, π, hπ⟩ := h
  have hπ' := hπ
  obtain ⟨hπs, hZU, -, hUinv, hZinv, -, -, -⟩ := hπ'
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord (D := FFModel.nat (StatedSL 3 K))
    rfl rfl hπ
  classical
  have := Fintype.ofFinite K
  have hcardK : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hcard, ZMod.card]; norm_num
  let e : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcardK
  have he1 : ∀ x : K, x ≠ 0 → x = 1 := by
    intro x hx
    have h1 : e x ≠ 0 := fun h => hx (e.injective (by rw [h, map_zero]))
    have h2 : e x = 1 := by
      generalize e x = y at h1
      revert y; decide
    exact e.injective (by rw [h2, map_one])
  let φ : ZMod 2 →+* K := (e.symm : ZMod 2 ≃+* K).toRingHom
  let ψ₀ : L3.Γ →* Matrix.GeneralLinearGroup (Fin 3) K :=
    (Matrix.SpecialLinearGroup.toGL).comp (Matrix.SpecialLinearGroup.map φ)
  have hψ : ∀ g, ψ₀ g ∈ StatedSL 3 K := by
    intro g
    apply Subgroup.subset_closure
    show ((Matrix.SpecialLinearGroup.map φ g : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1
    exact Matrix.SpecialLinearGroup.det_coe _
  let ψ : L3.Γ →* ↥(StatedSL 3 K) := ψ₀.codRestrict _ hψ
  have hψs : Function.Surjective (⇑ψ) := by
    intro b
    obtain ⟨A, hA⟩ := b
    have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      have h1 := he1 _ (Matrix.GeneralLinearGroup.det A).ne_zero
      simpa using h1
    let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := (A : Matrix (Fin 3) (Fin 3) K).map e
    have hM : M.det = 1 := by
      have h1 := RingHom.map_det e.toRingHom (A : Matrix (Fin 3) (Fin 3) K)
      rw [hdet, map_one] at h1
      exact h1.symm
    refine ⟨⟨M, hM⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    show (M.map φ) = (A : Matrix (Fin 3) (Fin 3) K)
    have hid : (⇑e.symm ∘ ⇑e : K → K) = id := funext fun x => e.symm_apply_apply x
    simp only [M, φ]
    show ((A : Matrix (Fin 3) (Fin 3) K).map e).map e.symm = A
    rw [Matrix.map_map, hid, Matrix.map_id]
  let π' : L3.Γ →* ↥G := π.comp ψ
  have hπ's : Function.Surjective π' := hπs.comp hψs
  let Φ : Multiplicative (Fin 3 → K) →* Multiplicative (Fin 3 → ZMod 2) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.compLeft (e.toRingHom : K →+* ZMod 2).toAddMonoidHom (Fin 3))
  have hΦ : ∀ x : Multiplicative (Fin 3 → K), Φ x = Multiplicative.ofAdd (fun i => e (Multiplicative.toAdd x i)) :=
    fun x => rfl
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    rw [hΦ, hΦ] at hxy
    have := Multiplicative.ofAdd.injective hxy
    apply Multiplicative.toAdd.injective
    funext i
    exact e.injective (congrFun this i)
  have hΦsurj : Function.Surjective Φ := by
    intro y
    refine ⟨Multiplicative.ofAdd (fun i => e.symm (Multiplicative.toAdd y i)), ?_⟩
    rw [hΦ]
    simp
  refine ⟨⟨π', Φ.comp β, hπ's, hΦsurj.comp hβs, ?_, hZU, fun g hg u hu => hUinv ⟨g, hg⟩ u hu,
    fun g hg z hz => hZinv ⟨g, hg⟩ z hz, ?_⟩⟩
  · intro u
    rw [← hβk u]
    show Φ (β u) = 1 ↔ β u = 1
    exact map_eq_one_iff Φ hΦinj
  · intro γ u hu
    have h1 := hβe (ψ γ) u hu
    show Φ (β ⟨((π' γ : ↥G) : MulAut V) (u : V), hu⟩) =
      Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd (Φ (β u))))
    have h2 : β ⟨((π' γ : ↥G) : MulAut V) (u : V), hu⟩ =
        natAct (StatedSL 3 K) (ψ γ) (β u) := h1
    rw [h2]
    show Multiplicative.ofAdd (fun i => e ((((ψ γ : Matrix.GeneralLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd (β u))) i)) =
      Multiplicative.ofAdd (L3.act γ (fun i => e (Multiplicative.toAdd (β u) i)))
    congr 1
    funext i
    simp [L3.act, Matrix.mulVec, dotProduct, map_sum, map_mul, ψ, ψ₀, φ]
    rfl


namespace L3Data

variable {G : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data G U Z)

@[expose] def rho : L3.Γ →* MulAut V := G.subtype.comp D.π

theorem rho_apply (γ : L3.Γ) (v : V) : D.rho γ v = ((D.π γ : ↥G) : MulAut V) v := rfl

theorem rho_mem (γ : L3.Γ) : D.rho γ ∈ G := (D.π γ).2

theorem exists_rho {g : MulAut V} (hg : g ∈ G) : ∃ γ, D.rho γ = g := by
  obtain ⟨γ, hγ⟩ := D.π_surj ⟨g, hg⟩
  exact ⟨γ, congrArg Subtype.val hγ⟩

theorem β_rho (γ : L3.Γ) (u : V) (hu : u ∈ U) (hu' : D.rho γ u ∈ U) :
    D.β ⟨D.rho γ u, hu'⟩ =
      Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd (D.β ⟨u, hu⟩))) :=
  D.equi γ ⟨u, hu⟩ hu'

theorem π_injective : Function.Injective D.π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply L3.act_injective
  intro w
  obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd w)
  have h1 : D.rho γ = 1 := by
    have : ((D.π γ : ↥G) : MulAut V) = 1 := by rw [hγ]; rfl
    exact this
  have hmem : D.rho γ (u : V) ∈ U := D.inv_U _ (D.rho_mem γ) _ u.2
  have h2 := D.β_rho γ (u : V) u.2 hmem
  have h3 : (⟨D.rho γ (u : V), hmem⟩ : ↥U) = u := by
    apply Subtype.ext
    show D.rho γ (u : V) = u
    rw [h1]; rfl
  rw [h3, hu] at h2
  have := Multiplicative.ofAdd.injective h2
  exact this.symm

theorem rho_injective : Function.Injective D.rho :=
  G.subtype_injective.comp D.π_injective

theorem le_of_gens {S : Subgroup (MulAut V)} (h1 : D.rho L3.x12 ∈ S) (h2 : D.rho L3.x23 ∈ S)
    (h3 : D.rho L3.x31 ∈ S) : G ≤ S := by
  intro g hg
  obtain ⟨γ, rfl⟩ := D.exists_rho hg
  have hcl : Subgroup.closure ({L3.x12, L3.x23, L3.x31} : Set L3.Γ) ≤ S.comap D.rho := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  rw [L3.closure_gens] at hcl
  exact hcl (Subgroup.mem_top γ)

theorem exists_invol {a : MulAut V} (ha : a ∈ G) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) :
    ∃ γ : L3.Γ, L3.IsInvol γ ∧ D.rho γ = a := by
  obtain ⟨γ, rfl⟩ := D.exists_rho ha
  refine ⟨γ, ⟨?_, ?_⟩, rfl⟩
  · apply D.rho_injective
    rw [map_mul, map_one, ← pow_two, ha2]
  · intro h
    apply ha1
    rw [h, map_one]

include D in
theorem exists_conj {a b : MulAut V} (ha : a ∈ G) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (hb : b ∈ G)
    (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) : ∃ g ∈ G, g * a * g⁻¹ = b := by
  obtain ⟨γ, hγ, rfl⟩ := D.exists_invol ha ha2 ha1
  obtain ⟨δ, hδ, rfl⟩ := D.exists_invol hb hb2 hb1
  obtain ⟨x, hx⟩ := L3.conj_invol hγ hδ
  refine ⟨D.rho x, D.rho_mem x, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hx]


theorem card_vec : Nat.card (Multiplicative L3.Vec) = 8 := by
  rw [Nat.card_eq_fintype_card]
  simp [ZMod.card]

theorem card_ker_β : Nat.card D.β.ker = Nat.card Z := by
  refine Nat.card_congr ⟨fun u => ⟨u.1.1, (D.ker_β u.1).1 u.2⟩,
    fun z => ⟨⟨z.1, D.Z_le z.2⟩, (D.ker_β _).2 z.2⟩, ?_, ?_⟩
  · intro u
    rfl
  · intro z
    rfl

include D in
theorem card_U : Nat.card U = 8 * Nat.card Z := by
  have h := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥U) D.β
  have h1 : (⊤ : Subgroup ↥U).map D.β = ⊤ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top]
    exact D.β_surj
  rw [h1, top_inf_eq, Subgroup.card_top, Subgroup.card_top, card_vec, card_ker_β] at h
  exact h.symm

end L3Data

end CFSG.Quasithin
