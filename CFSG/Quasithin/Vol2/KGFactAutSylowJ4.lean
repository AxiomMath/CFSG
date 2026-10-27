module

public import CFSG.Sporadic.Schreier.J4SOuter
public import CFSG.Sporadic.J4.QTOutAuto
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Quasithin.Vol2.KGFactAutSylowSmall

public section

namespace CFSG.Quasithin.H13.KGAutSyl

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms

theorem normalizer_le_of_isPGroup_mulAut {Y : Type} [Group Y] [Finite Y] (S : Sylow 2 Y)
    (hAut : IsPGroup 2 (MulAut ↥(S : Subgroup Y)))
    (hC : Subgroup.centralizer ((S : Subgroup Y) : Set Y) ≤ S) :
    Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha
  set σ := KG68.conjOn (S : Subgroup Y) a ha with hσ
  obtain ⟨k, hk⟩ := hAut σ
  have hpow : ∀ j : ℕ, ∀ x : ↥(S : Subgroup Y),
      (((σ ^ j) x : ↥(S : Subgroup Y)) : Y) = a ^ j * x * (a ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hσ, KG68.conjOn_coe, ← hσ, ih x]
      group
  have hcent : a ^ 2 ^ k ∈ Subgroup.centralizer ((S : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hpow (2 ^ k) ⟨x, hx⟩
    rw [hk] at h1
    have h2 : x = a ^ 2 ^ k * x * (a ^ 2 ^ k)⁻¹ := h1
    calc x * a ^ 2 ^ k = (a ^ 2 ^ k * x * (a ^ 2 ^ k)⁻¹) * a ^ 2 ^ k := by rw [← h2]
      _ = a ^ 2 ^ k * x := by group
  obtain ⟨j, hj⟩ := S.isPGroup' ⟨_, hC hcent⟩
  have ha2 : a ^ 2 ^ (k + j) = 1 := by
    rw [pow_add, pow_mul]
    simpa using congrArg Subtype.val hj
  have hK : IsPGroup 2 (Subgroup.zpowers a) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one ha2)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hle : Subgroup.zpowers a ≤ Subgroup.normalizer ((S : Subgroup Y) : Set Y) :=
    (Subgroup.zpowers_le).mpr ha
  have heq := S.is_maximal' (IsPGroup.to_sup_of_normal_left' S.isPGroup' hK hle) le_sup_left
  show a ∈ (S : Subgroup Y)
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)

theorem normalizer_inf_le_of_maps_inner {G : Type*} [Group G] [Finite G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hsn : ∀ P : Subgroup G, IsSylowTwoOf P ⊤ → Subgroup.normalizer (P : Set G) ≤ P)
    (hmaps : ∀ P : Subgroup G, IsSylowTwoOf P ⊤ → ∀ α : MulAut G, (∀ x ∈ P, α x ∈ P) →
      α ∈ inner G)
    {A S : Subgroup (MulAut G)} (hA : (MulAut.conj : G →* MulAut G).range ≤ A)
    (hS : IsSylowTwoOf S A) : Subgroup.normalizer (S : Set (MulAut G)) ⊓ A ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨hxN, -⟩ := Subgroup.mem_inf.mp hx
  have hSI : IsSylowTwoOf (S ⊓ inner G) (inner G) :=
    A4.isSylowTwoOf_inf_normal hS hA (fun g _ => Subgroup.mem_normalizer_iff.mpr fun h =>
      ⟨fun hh => (inner_normal G).conj_mem h hh g, fun hh => by
        have := (inner_normal G).conj_mem _ hh g⁻¹
        simpa [mul_assoc] using this⟩)
  have hxNI : x ∈ Subgroup.normalizer ((S ⊓ inner G : Subgroup (MulAut G)) : Set (MulAut G)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hxN h]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (inner_normal G).conj_mem h h2 x⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := (inner_normal G).conj_mem _ h2 x⁻¹
      simpa [mul_assoc] using this
  let φ : G →* ↥(inner G) :=
    (MulAut.conj : G →* MulAut G).codRestrict (inner G) fun x => ⟨x, rfl⟩
  have hφ : ∀ g, (φ g : MulAut G) = MulAut.conj g := fun g => rfl
  let P : Subgroup G := ((S ⊓ inner G).subgroupOf (inner G)).comap φ
  have hmem : ∀ g : G, g ∈ P ↔ MulAut.conj g ∈ S ⊓ inner G := fun g => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hφ]
  have hφinj : Function.Injective φ := fun a b hab => hinj (by rw [← hφ a, ← hφ b, hab])
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, g, rfl⟩
    exact ⟨g, rfl⟩
  have hPsyl : IsSylowTwoOf P ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact (hSI.2.1.comap_of_injective (inner G).subtype Subtype.val_injective).comap_of_injective
        φ hφinj
    · have h1 : P.index = ((S ⊓ inner G).subgroupOf (inner G)).index :=
        Subgroup.index_comap_of_surjective _ hφsurj
      show ¬ 2 ∣ P.relIndex ⊤
      rw [Subgroup.relIndex_top_right, h1]
      exact hSI.2.2
  have hxI : x ∈ inner G := by
    refine hmaps P hPsyl x fun g hg => ?_
    rw [hmem] at hg ⊢
    have e : MulAut.conj (x g) = x * MulAut.conj g * x⁻¹ := by
      ext y
      simp [MulAut.conj_apply, map_mul, map_inv]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hxNI _).mp hg
  exact (Subgroup.mem_inf.mp (KGHe.mem_of_mem_normalizer_inner hinj hsn hSI hxI hxNI)).1

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4 in
theorem j4_normalizer_S0 :
    Subgroup.normalizer ((S0Sylow : Subgroup J) : Set J) = S0Sylow := by
  refine le_antisymm (normalizer_le_of_isPGroup_mulAut S0Sylow
    (R3E_J4_Sylow_two_automorphism_group_is_two_group S0Sylow).2 ?_) Subgroup.le_normalizer
  have hCN : Subgroup.centralizer (N : Set J) = N := by
    have h := QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2
    have hle : Subgroup.centralizer (N : Set J) ≤ H := by
      rw [← normalizer_N]
      exact Subgroup.centralizer_le_normalizer _
    exact (inf_eq_left.mpr hle).symm.trans h
  have hNS : (N : Subgroup J) ≤ S0Sylow := by
    rw [S0Sylow_coe]
    exact N_le_S0
  intro x hx
  have hxN : x ∈ Subgroup.centralizer (N : Set J) := Subgroup.centralizer_le hNS hx
  rw [hCN] at hxN
  exact hNS hxN

theorem mem_inner_of_forall {G : Type*} [Group G] {α : MulAut G}
    (h : ∃ k : G, ∀ x, α x = k * x * k⁻¹) : α ∈ inner G := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, MulEquiv.ext fun x => by rw [MulAut.conj_apply, hk]⟩

theorem maps_inner_of_maps_inner {G : Type} [Group G] [Finite G] (P₀ : Sylow 2 G)
    (h₀ : ∀ α : MulAut G, (∀ x ∈ (P₀ : Subgroup G), α x ∈ (P₀ : Subgroup G)) → α ∈ inner G)
    (P : Subgroup G) (hP : IsSylowTwoOf P ⊤) (α : MulAut G) (hα : ∀ x ∈ P, α x ∈ P) :
    α ∈ inner G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hPi⟩ := K1.isSylowTwoOf_top_iff.mp hP
  let P' : Sylow 2 G := hP2.toSylow hPi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' P₀
  have hmap : P.map (MulAut.conj g).toMonoidHom = P₀ := by
    have := congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) hg
    exact this
  have hβapp : ∀ z, (MulAut.conj g * α * (MulAut.conj g)⁻¹) z = g * α (g⁻¹ * z * g) * g⁻¹ :=
    fun z => by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
  have hβ := h₀ (MulAut.conj g * α * (MulAut.conj g)⁻¹) fun y hy => by
    rw [← hmap] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨α x, hα x hx, ?_⟩
    rw [hβapp]
    show g * α x * g⁻¹ = g * α (g⁻¹ * (g * x * g⁻¹) * g) * g⁻¹
    rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  have e : α = (MulAut.conj g)⁻¹ * (MulAut.conj g * α * (MulAut.conj g)⁻¹) * MulAut.conj g := by
    group
  rw [e]
  exact (inner G).mul_mem ((inner G).mul_mem ((inner G).inv_mem ⟨g, rfl⟩) hβ) ⟨g, rfl⟩

open CFSG.Sporadic.J4 in
theorem j4_maps_inner
    (P : Subgroup J) (hP : IsSylowTwoOf P ⊤) (α : MulAut J)
    (hα : ∀ x ∈ P, α x ∈ P) : α ∈ inner J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := j4Facts
  refine maps_inner_of_maps_inner (Sylow.ofCard QT.P0 (by
    rw [QT.card_P0 hF.mat hF, QT.card_J_factorization hF])) (fun β hβ => ?_) P hP α hα
  rw [Sylow.coe_ofCard] at hβ
  exact mem_inner_of_forall (QT.aut_of_maps_P0 hF β hβ)

theorem maps_inner_of_mulEquiv {G H : Type} [Group G] [Group H] [Finite G] (e : G ≃* H)
    (h : ∀ P : Subgroup H, IsSylowTwoOf P ⊤ → ∀ α : MulAut H, (∀ x ∈ P, α x ∈ P) → α ∈ inner H)
    (P : Subgroup G) (hP : IsSylowTwoOf P ⊤) (α : MulAut G) (hα : ∀ x ∈ P, α x ∈ P) :
    α ∈ inner G := by
  have : Finite H := Finite.of_equiv G e.toEquiv
  let α' : MulAut H := (e.symm.trans α).trans e
  have hα'app : ∀ y, α' y = e (α (e.symm y)) := fun y => rfl
  have hP' := CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map e hP
  obtain ⟨k, hk⟩ := h _ hP' α' fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨α x, hα x hx, ?_⟩
    rw [hα'app]
    show e (α x) = e (α (e.symm (e x)))
    rw [MulEquiv.symm_apply_apply]
  refine ⟨e.symm k, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun φ : MulAut H => φ (e x)) hk
  simp only [MulAut.conj_apply] at h1
  rw [hα'app, MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4 in
theorem factAutSylowJ4_holds :
    FactAutSylowJ4 := by
  intro Q _ _ hQ A S hA hS
  obtain ⟨e⟩ := hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eJ : Q ≃* J := e.trans (seedEquiv j4Facts.mat)
  have : Finite J := Finite.of_equiv Q eJ.toEquiv
  have hsJ := j4_normalizer_S0
  obtain ⟨P₀, hP₀⟩ := @CFSG.LieType.SteinbergBR.OddSylow.exists_selfNormalizing_of_equiv Q _ _ J
    (Subgroup.toGroup J) _ 2 _ eJ S0Sylow hsJ
  have hZ : Subgroup.center Q = ⊥ := by
    have hQs : IsSimpleGroup Q :=
      @MulEquiv.isSimpleGroup Q _ J (Subgroup.toGroup J) (isSimpleGroup_J j4Facts) eJ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      have hN : (P₀ : Subgroup Q).Normal := ⟨fun p hp g => by
        have hg : g ∈ Subgroup.center Q := h ▸ Subgroup.mem_top g
        rw [(Subgroup.mem_center_iff.mp hg p).symm]
        simpa using hp⟩
      have htop : Subgroup.normalizer ((P₀ : Subgroup Q) : Set Q) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr hN
      have h4 : (P₀ : Subgroup Q) = ⊤ := hP₀.symm.trans htop
      have h1 : Nat.card (P₀ : Subgroup Q) = Nat.card Q := by rw [h4, Subgroup.card_top]
      have h2 : Nat.card (P₀ : Subgroup Q) = 2 ^ 21 := by
        rw [P₀.card_eq_multiplicity, Nat.card_congr eJ.toEquiv, factorization_card_J]
      have h3 : Nat.card Q = 86775571046077562880 := by
        rw [Nat.card_congr eJ.toEquiv, card_J4J]
      omega
  exact normalizer_inf_le_of_maps_inner (KG68.conj_injective_of_center hZ)
    (selfNormalizing_of_exists ⟨P₀, hP₀⟩)
    (@maps_inner_of_mulEquiv Q J _ (Subgroup.toGroup J) _ eJ j4_maps_inner) hA hS

end CFSG.Quasithin.H13.KGAutSyl
