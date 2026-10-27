module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwo
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Hyperplane
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.Quasithin.Background.E1Sec6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] [Finite G]

private theorem four_le_card_of_not_isCyclic' {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hnc : ¬ IsCyclic A) : 4 ≤ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp : IsPGroup 2 A := hA.isPGroup
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  rcases k with _ | _ | k
  · exfalso
    apply hnc
    have : Subsingleton ↥A := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    infer_instance
  · exfalso
    exact hnc (isCyclic_of_prime_card (by simpa using hk))
  · rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem commutator_le_centralizer_of_le_centralizer {A B E : Subgroup G}
    (hAE : A ≤ Subgroup.normalizer (E : Set G)) (hBE : B ≤ Subgroup.normalizer (E : Set G))
    (hB : B ≤ Subgroup.centralizer (E : Set G)) :
    ⁅A, B⁆ ≤ Subgroup.centralizer (E : Set G) := by
  have hBEbot : ⁅B, E⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hB
  have hEA : ⁅E, A⁆ ≤ E := by
    refine Subgroup.commutator_le.mpr fun e he a ha => ?_
    have hmem : a * e⁻¹ * a⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hAE ha) e⁻¹).1 (E.inv_mem he)
    have heq : ⁅e, a⁆ = e * (a * e⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact E.mul_mem he hmem
  have h1 : ⁅⁅B, E⁆, A⁆ = ⊥ := by rw [hBEbot, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅E, A⁆, B⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hB.trans (Subgroup.centralizer_le hEA)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := A) (H₂ := B) (H₃ := E) h1 h2
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

theorem commutator_le_centralizer_of_inf_centralizer_eq {E A Q : Subgroup G}
    (hE : IsElemAbelian 2 E) (hA : IsElemAbelian 2 A)
    (hAnc : ¬ IsCyclic A) (hAE : A ≤ Subgroup.normalizer (E : Set G))
    (hAE0 : ∀ a ∈ A, a ≠ 1 →
      E ⊓ Subgroup.centralizer ({a} : Set G) = E ⊓ Subgroup.centralizer (A : Set G))
    (hQodd : Odd (Nat.card Q)) (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hQE : Q ≤ Subgroup.normalizer (E : Set G)) :
    ⁅Q, A⁆ ≤ Subgroup.centralizer (E : Set G) := by
  classical
  have hA4 : 4 ≤ Nat.card A := four_le_card_of_not_isCyclic' hA hAnc
  have hA2 : 2 ^ 2 ≤ Nat.card A := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact hA4
  have hcopQ : Nat.Coprime 2 (Nat.card Q) := Nat.coprime_two_left.mpr hQodd
  have hgen : ⨆ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 A,
      Q ⊓ Subgroup.centralizer (B : Set G) = Q :=
    CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.generation_hyperplanes
      Nat.prime_two hA hA2 hAQ hcopQ
  set E0 : Subgroup G := E ⊓ Subgroup.centralizer (A : Set G) with hE0def
  have hE0B : ∀ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 A,
      E ⊓ Subgroup.centralizer (B : Set G) = E0 := by
    intro B hB
    have hBne : B ≠ ⊥ := by
      intro hbot
      have hcard := hB.2
      rw [hbot, Subgroup.card_bot, mul_one] at hcard
      omega
    obtain ⟨b, hb1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
    have hbB : (b : G) ∈ B := b.2
    have hb1 : (b : G) ≠ 1 := fun h => hb1' (Subtype.ext h)
    rw [hE0def]
    refine le_antisymm ?_ ?_
    · refine (inf_le_inf_left E
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))).trans ?_
      exact le_of_eq (hAE0 (b : G) (hB.1 hbB) hb1)
    · exact inf_le_inf_left E (Subgroup.centralizer_le hB.1)
  have hQE0 : Q ≤ Subgroup.normalizer (E0 : Set G) := by
    rw [← hgen]
    refine iSup_le fun B => iSup_le fun hB => ?_
    intro x hx
    have hxE : x ∈ Subgroup.normalizer (E : Set G) := hQE hx.1
    have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) :=
      Subgroup.le_normalizer hx.2
    have hmem := Subgroup.inf_normalizer_le_normalizer_inf
      (show x ∈ Subgroup.normalizer (E : Set G) ⊓
        Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) from ⟨hxE, hxC⟩)
    rwa [hE0B B hB] at hmem
  set Q1 : Subgroup G := ⁅Q, A⁆ with hQ1def
  have hQ1le : Q1 ≤ Q := by
    rw [hQ1def]
    refine Subgroup.commutator_le.mpr fun q hq a ha => ?_
    have haq : a * q⁻¹ * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hAQ ha) q⁻¹).1 (Q.inv_mem hq)
    have heq : ⁅q, a⁆ = q * (a * q⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact Q.mul_mem hq haq
  have hQ1E : Q1 ≤ Subgroup.normalizer (E : Set G) := hQ1le.trans hQE
  have hQ1E0 : Q1 ≤ Subgroup.centralizer (E0 : Set G) := by
    rw [hQ1def]
    refine Subgroup.commutator_le.mpr fun q hq a ha => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hxE : x ∈ E := hx.1
    have hxC_A : x ∈ Subgroup.centralizer (A : Set G) := hx.2
    have hax : a * x * a⁻¹ = x := by
      have := Subgroup.mem_centralizer_iff.mp hxC_A a ha
      calc a * x * a⁻¹ = (x * a) * a⁻¹ := by rw [this]
        _ = x := by group
    have hqx : q⁻¹ * x * q ∈ E0 :=
      (Subgroup.mem_normalizer_iff''.mp (hQE0 hq) x).mp hx
    have haqx : a * (q⁻¹ * x * q) * a⁻¹ = q⁻¹ * x * q := by
      have hmem : q⁻¹ * x * q ∈ Subgroup.centralizer (A : Set G) := hqx.2
      have := Subgroup.mem_centralizer_iff.mp hmem a ha
      calc a * (q⁻¹ * x * q) * a⁻¹ = ((q⁻¹ * x * q) * a) * a⁻¹ := by rw [this]
        _ = q⁻¹ * x * q := by group
    have hconj : ⁅q, a⁆ * x * ⁅q, a⁆⁻¹ = x := by
      rw [commutatorElement_def]
      have hax' : a⁻¹ * x * a = x := by
        calc a⁻¹ * x * a = a⁻¹ * (a * x * a⁻¹) * a := by rw [hax]
          _ = x := by group
      rw [show (q * a * q⁻¹ * a⁻¹)⁻¹ = a * q * a⁻¹ * q⁻¹ by group]
      rw [show q * a * q⁻¹ * a⁻¹ * x * (a * q * a⁻¹ * q⁻¹) =
          q * a * q⁻¹ * (a⁻¹ * x * a) * q * a⁻¹ * q⁻¹ by group]
      rw [hax']
      rw [show q * a * q⁻¹ * x * q * a⁻¹ * q⁻¹ =
          q * (a * (q⁻¹ * x * q) * a⁻¹) * q⁻¹ by group]
      rw [haqx]
      group
    have h1 : ⁅q, a⁆ * x = x * ⁅q, a⁆ := by
      calc ⁅q, a⁆ * x = ⁅q, a⁆ * x * ⁅q, a⁆⁻¹ * ⁅q, a⁆ := by group
        _ = x * ⁅q, a⁆ := by rw [hconj]
    exact h1.symm
  have hPE : ⁅E, Q1⁆ ≤ E := by
    refine Subgroup.commutator_le.mpr fun e he q hq => ?_
    have hmem : q * e⁻¹ * q⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hQ1E hq) e⁻¹).1 (E.inv_mem he)
    have heq : ⁅e, q⁆ = e * (q * e⁻¹ * q⁻¹) := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact E.mul_mem he hmem
  have hP2 : IsPGroup 2 ↥(⁅E, Q1⁆) := hE.isPGroup.to_le hPE
  have hAQ1 : A ≤ Subgroup.normalizer (Q1 : Set G) :=
    CFSG.Quasithin.E1.le_normalizer_commutator_right hAQ
  have hAP : A ≤ Subgroup.normalizer ((⁅E, Q1⁆ : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator]
    congr 1
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAE ha)
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAQ1 ha)
  have hdisj : E ⊓ Subgroup.centralizer (Q1 : Set G) ⊓ ⁅Q1, E⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxCE, hxP⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.mp hxCE
    refine CFSG.LocalAnalysis.EvenBN.Common.mem_of_mem_commutator_sup_of_fixed
      (A := Q1) (Y := E) (Z := ⊥) bot_le ?_ hQ1E (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      ?_ (Subgroup.mem_sup_left hxP) ?_
    · intro y hy y' hy'
      refine Subgroup.mem_bot.mpr ?_
      have hcomm : y * y' = y' * y :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
      calc y * y' * y⁻¹ * y'⁻¹ = (y * y') * (y' * y)⁻¹ := by group
        _ = 1 := by rw [hcomm]; group
    · obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
      rw [hk]
      exact (((Nat.coprime_two_left.mpr hQodd).coprime_dvd_right
        (Subgroup.card_dvd_of_le hQ1le)).symm).pow_right k
    · intro a ha
      refine Subgroup.mem_bot.mpr ?_
      have hcomm : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxC a ha
      rw [hcomm]; group
  have hdisjE : ⁅E, Q1⁆ ⊓ (E ⊓ Subgroup.centralizer (Q1 : Set G)) = ⊥ := by
    rw [Subgroup.commutator_comm E Q1, inf_comm]
    exact hdisj
  have hPbot : ⁅E, Q1⁆ = ⊥ := by
    by_contra hPne
    have hne : ¬ ⁅E, Q1⁆ ≤ (⊥ : Subgroup G) := fun h => hPne (le_bot_iff.mp h)
    obtain ⟨x, hxP, hxne, hxfix⟩ :=
      CFSG.LocalAnalysis.EvenBN.Common.exists_mem_forall_conj_mem_of_isPGroup
        (p := 2) (R := A) (H := ⁅E, Q1⁆) (N := ⊥) hA.isPGroup hP2 bot_le hne hAP
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    have hxC_A : x ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 : a * x * a⁻¹ = x := by
        have := congrArg (fun t => x * t) (Subgroup.mem_bot.mp (hxfix a ha))
        simpa [mul_assoc] using this
      calc a * x = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h1]
    have hxE0 : x ∈ E0 := Subgroup.mem_inf.mpr ⟨hPE hxP, hxC_A⟩
    have hxC_Q1 : x ∈ Subgroup.centralizer (Q1 : Set G) :=
      (Subgroup.le_centralizer_iff.mp hQ1E0) hxE0
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hdisjE]
      exact Subgroup.mem_inf.mpr ⟨hxP, Subgroup.mem_inf.mpr ⟨hPE hxP, hxC_Q1⟩⟩
    exact hxne (Subgroup.mem_bot.mp hxbot)
  have hQ1cent : Q1 ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPbot)
  exact hQ1cent

theorem wClos_zero_eq_iSup {V X : Subgroup G} (hV : IsElemAbelian 2 V) :
    E3.wClos V 0 X = ⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g := by
  refine le_antisymm ?_ ?_
  · rw [E3.wClos]
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAX, g, hAg, hm⟩ := hA
    have hAV : A = conjSubgroup V g :=
      (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV.isPGroup g) hAg).1 hm
    rw [hAV]
    exact le_iSup₂_of_le g (hAV ▸ hAX) le_rfl
  · refine iSup₂_le fun g hg => ?_
    rw [E3.wClos]
    exact le_iSup₂_of_le (conjSubgroup V g) ⟨hg, g, le_rfl, E3.mQuot_self _⟩ le_rfl

theorem conjSubgroup_le_wClos_zero {V X : Subgroup G} {g : G} (hg : conjSubgroup V g ≤ X) :
    conjSubgroup V g ≤ E3.wClos V 0 X := by
  rw [E3.wClos]
  exact le_iSup₂_of_le (conjSubgroup V g) ⟨hg, g, le_rfl, E3.mQuot_self _⟩ le_rfl

theorem wClos_zero_le (V X : Subgroup G) : E3.wClos V 0 X ≤ X := by
  rw [E3.wClos]
  exact iSup₂_le fun _ hA => hA.1

private theorem coe_conjSubgroup_of_conjSet {X : Type*} [Group X] {A : Subgroup X} (g : X) :
    (conjSubgroup A g : Set X) = conjSet (A : Set X) g := by
  ext x
  rw [SetLike.mem_coe, CFSG.Quasithin.mem_conjSubgroup_iff, mem_conjSet_iff, SetLike.mem_coe]

theorem map_conjSubgroup_subgroupOf {A H : Subgroup G} (hAH : A ≤ H) {x : G} (hx : x ∈ H) :
    (conjSubgroup (A.subgroupOf H) ⟨x, hx⟩).map H.subtype = conjSubgroup A x := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    simpa using hz
  · intro hy
    have hyH : y ∈ H := conjSubgroup_le_of_le hAH hx hy
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hy
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    rw [CFSG.Quasithin.mem_conjSubgroup_iff, Subgroup.mem_subgroupOf]
    simpa using hy

private theorem map_subtype_injective' {H : Subgroup G} {A B : Subgroup ↥H}
    (h : A.map H.subtype = B.map H.subtype) : A = B := by
  ext x
  constructor
  · intro hx
    have hx' : H.subtype x ∈ A.map H.subtype := ⟨x, hx, rfl⟩
    rw [h] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    have : y = x := Subtype.ext hxy
    rwa [this] at hy
  · intro hx
    have hx' : H.subtype x ∈ B.map H.subtype := ⟨x, hx, rfl⟩
    rw [← h] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    have : y = x := Subtype.ext hxy
    rwa [this] at hy

private theorem iSup_conjSubgroup_isWeaklyClosedIn (V X : Subgroup G) :
    IsWeaklyClosedIn (⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g) X := by
  intro x hx
  have h1 : conjSubgroup (⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g) x ≤
      ⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g := by
    have hmap : conjSubgroup (⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g) x =
        ⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V (g * x) := by
      rw [show conjSubgroup (⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g) x =
          (⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g).map
            (MulAut.conj x⁻¹).toMonoidHom from rfl]
      rw [Subgroup.map_iSup]
      refine iSup_congr fun g => ?_
      rw [Subgroup.map_iSup]
      refine iSup_congr fun hg => ?_
      show (conjSubgroup V g).map (MulAut.conj x⁻¹).toMonoidHom = conjSubgroup V (g * x)
      exact conjSubgroup_conjSubgroup V g x
    rw [hmap]
    refine iSup₂_le fun g hg => ?_
    refine le_iSup₂_of_le (g * x) ?_ le_rfl
    calc conjSubgroup V (g * x) = conjSubgroup (conjSubgroup V g) x :=
          (conjSubgroup_conjSubgroup V g x).symm
      _ ≤ conjSubgroup (⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g) x :=
          Subgroup.map_mono (le_iSup₂_of_le g hg le_rfl)
      _ ≤ X := hx
  refine Subgroup.eq_of_le_of_card_ge h1 ?_
  rw [show conjSubgroup (⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g) x =
      (⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g).map
        (MulAut.conj x⁻¹).toMonoidHom from rfl]
  exact (Subgroup.card_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
    (MulAut.conj x⁻¹).injective).ge

theorem wClos_zero_isWeaklyClosedIn {V X : Subgroup G} (hV : IsElemAbelian 2 V) :
    IsWeaklyClosedIn (E3.wClos V 0 X) X := by
  rw [wClos_zero_eq_iSup (X := X) hV]
  exact iSup_conjSubgroup_isWeaklyClosedIn V X

theorem exists_conjSubgroup_eq_of_weaklyClosedIn {V W T H : Subgroup G}
    (hWT : W ≤ T) (hWH : W ≤ H) (hTH : T ≤ H)
    (hwc : ∀ x ∈ H, conjSubgroup W x ≤ T → conjSubgroup W x = W)
    (hT : IsSylowIn 2 T H) (hVH : V ≤ H)
    (hWV : W ≤ Subgroup.normalizer (V : Set G))
    {h : G} (hh : h ∈ H)
    (hWVh : W ≤ Subgroup.normalizer (conjSubgroup V h : Set G)) :
    ∃ n ∈ H ⊓ Subgroup.normalizer (W : Set G), conjSubgroup V n = conjSubgroup V h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set WJ : Subgroup ↥H := W.subgroupOf H with hWJdef
  set VJ : Subgroup ↥H := V.subgroupOf H with hVJdef
  set BJ : Subgroup ↥H := (conjSubgroup V h).subgroupOf H with hBJdef
  have hwcJ : IsWeaklyClosedIn WJ (hT.toSylow : Subgroup ↥H) := by
    intro x hxle
    rw [IsSylowIn.coe_toSylow] at hxle
    have hxG : (x : G) ∈ H := x.2
    have hxle' : conjSubgroup W (x : G) ≤ T := by
      have h1 : (conjSubgroup WJ x).map H.subtype ≤ (T.subgroupOf H).map H.subtype :=
        Subgroup.map_mono hxle
      rw [hWJdef] at h1
      rwa [map_conjSubgroup_subgroupOf hWH hxG, Subgroup.map_subgroupOf_eq_of_le hTH] at h1
    have heqW : conjSubgroup W (x : G) = W := hwc (x : G) hxG hxle'
    have hmap : (conjSubgroup WJ x).map H.subtype = WJ.map H.subtype := by
      rw [hWJdef]
      rw [map_conjSubgroup_subgroupOf hWH hxG, heqW, Subgroup.map_subgroupOf_eq_of_le hWH]
    exact map_subtype_injective' hmap
  have hWTJ : WJ ≤ (hT.toSylow : Subgroup ↥H) := by
    rw [hWJdef, IsSylowIn.coe_toSylow]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hWT hx
  have hAeq : ∀ w ∈ WJ, conjSet (VJ : Set ↥H) w = (VJ : Set ↥H) := by
    intro w hw
    rw [hVJdef]
    have hw' : (w : G) ∈ W := by
      rwa [hWJdef, Subgroup.mem_subgroupOf] at hw
    ext z
    rw [mem_conjSet_iff]
    change w * z * w⁻¹ ∈ V.subgroupOf H ↔ z ∈ V.subgroupOf H
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hWV hw') (z : G)).symm
  have hBeq : ∀ w ∈ WJ, conjSet (BJ : Set ↥H) w = (BJ : Set ↥H) := by
    intro w hw
    rw [hBJdef]
    have hw' : (w : G) ∈ W := by
      rwa [hWJdef, Subgroup.mem_subgroupOf] at hw
    ext z
    rw [mem_conjSet_iff]
    change w * z * w⁻¹ ∈ (conjSubgroup V h).subgroupOf H ↔
      z ∈ (conjSubgroup V h).subgroupOf H
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hWVh hw') (z : G)).symm
  have hgeq : conjSet (VJ : Set ↥H) ⟨h, hh⟩ = (BJ : Set ↥H) := by
    rw [hVJdef, hBJdef, ← coe_conjSubgroup_of_conjSet (X := ↥H) (A := V.subgroupOf H) ⟨h, hh⟩]
    have hsub : conjSubgroup (V.subgroupOf H) ⟨h, hh⟩ = (conjSubgroup V h).subgroupOf H := by
      apply map_subtype_injective'
      rw [map_conjSubgroup_subgroupOf hVH hh,
        Subgroup.map_subgroupOf_eq_of_le (conjSubgroup_le_of_le hVH hh)]
    exact congrArg (fun K : Subgroup ↥H => (K : Set ↥H)) hsub
  obtain ⟨n, hn, hneq⟩ := CFSG.Quasithin.burnside_fusion_lemma (p := 2) hT.toSylow hWTJ hwcJ
    hAeq hBeq hgeq
  refine ⟨(n : G), Subgroup.mem_inf.mpr ⟨n.2, ?_⟩, ?_⟩
  · rw [← conjSubgroup_eq_iff_mem_normalizer]
    have h1 : conjSubgroup WJ n = WJ := conjSubgroup_eq_iff_mem_normalizer.mpr hn
    have h2 := congrArg (Subgroup.map H.subtype) h1
    rw [hWJdef] at h2
    rwa [map_conjSubgroup_subgroupOf hWH n.2, Subgroup.map_subgroupOf_eq_of_le hWH] at h2
  · have hsub : conjSubgroup VJ n = BJ := by
      apply Subgroup.ext
      intro z
      have hz := Set.ext_iff.mp hneq z
      rw [mem_conjSet_iff] at hz
      rw [CFSG.Quasithin.mem_conjSubgroup_iff]
      exact hz
    have h2 := congrArg (Subgroup.map H.subtype) hsub
    rw [hVJdef, hBJdef] at h2
    rwa [map_conjSubgroup_subgroupOf hVH n.2,
      Subgroup.map_subgroupOf_eq_of_le (conjSubgroup_le_of_le hVH hh)] at h2

end CFSG.LocalAnalysis.WeakClosure81

end
