module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownAux
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification

open scoped commutatorElement

section Rigidity

variable {G : Type} [Group G]

theorem ggMem_normalizer_of_component [Finite G] {H K : Subgroup G} {r g : G}
    (hK : IsComponentOf K H) (hrK : r ∈ K) (hr : r ∉ Subgroup.centralizer (K : Set G))
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgr : g * r = r * g) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  have hK' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hK g
  rw [map_conj_eq_of_mem_normalizer hgH] at hK'
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK' hK with h | h
  · exact mem_normalizer_iff_map_conj.mpr h
  · exfalso
    apply hr
    have hle : K.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    refine hle (Subgroup.mem_map.mpr ⟨r, hrK, ?_⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hgr]
    group

theorem ggMem_normalizer_of_pComponent [Finite G] {p : ℕ} [Fact p.Prime] {e g r : G}
    {J K : Subgroup G}
    (hK : LargeEvenPComponent p (Subgroup.centralizer ({e} : Set G)) K) (hJK : J ≤ K)
    (hJq : CFSG.Assembly.IsQuasisimple J) (hpJ : p ∣ Nat.card J) (hrJ : r ∈ J)
    (hrC : r ∉ Subgroup.centralizer (J : Set G))
    (hge : g ∈ Subgroup.centralizer ({e} : Set G)) (hgr : g * r = r * g) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  have hp : p.Prime := Fact.out
  set Y := Subgroup.centralizer ({e} : Set G) with hYdef
  set O := CFSG.Open.lBalancePrimeCore p Y with hOdef
  have hON : Y ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (LBalance.primeCore_le p Y)).mp
      (LBalance.primeCore_normal p Y)
  have hKY : K ≤ Y := hK.1
  have hJY : J ≤ Y := hJK.trans hKY
  have hrK : r ∈ K := hJK hrJ
  have hrY : r ∈ Y := hKY hrK
  set K₁ := K.map (MulAut.conj g).toMonoidHom with hK₁def
  have hK₁ : LargeEvenPComponent p Y K₁ := largeEvenPComponent_map_conj hK hge
  by_contra hgK
  have hne : K₁ ≠ K := fun h => hgK (mem_normalizer_iff_map_conj.mpr h)
  have hrK₁ : r ∈ K₁ := by
    refine Subgroup.mem_map.mpr ⟨r, hrK, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hgr]
    group
  have hrO : ∀ k ∈ K, k * r * k⁻¹ * r⁻¹ ∈ O := by
    intro k hk
    rw [← commutatorElement_def]
    exact commutator_le_lBalancePrimeCore_of_ne hK hK₁ hne.symm
      (Subgroup.commutator_mem_commutator hk hrK₁)
  have hJO : (⁅J, Subgroup.zpowers r⁆ : Subgroup G) ≤ O :=
    (Subgroup.commutator_mono hJK le_rfl).trans
      (commutator_zpowers_le_of_forall (hON hrY) hrO)
  exact hrC (mem_centralizer_of_commutator_le_coprime hp hJq hpJ
    (LBalance.primeCore_coprime p Y) (hJY.trans hON) (Subgroup.le_normalizer hrJ) hJO)

end Rigidity

section Pieces

variable {G : Type} [Group G]

theorem ggMemNormalizerInf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
  have h1 := Subgroup.mem_normalizer_iff.mp hA h
  have h2 := Subgroup.mem_normalizer_iff.mp hB h
  simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
  rw [h1, h2]

@[expose] def ggActTrivMod (A E : Subgroup G) : Subgroup G where
  carrier := {w | w ∈ Subgroup.normalizer (A : Set G) ∧ w ∈ Subgroup.normalizer (E : Set G) ∧
    ∀ a ∈ A, w * a * w⁻¹ * a⁻¹ ∈ E}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun a _ => by simpa using E.one_mem⟩
  mul_mem' := by
    rintro w w' ⟨hwA, hwE, hw⟩ ⟨hw'A, hw'E, hw'⟩
    refine ⟨Subgroup.mul_mem _ hwA hw'A, Subgroup.mul_mem _ hwE hw'E, fun a ha => ?_⟩
    have e : w * w' * a * (w * w')⁻¹ * a⁻¹ =
        (w * (w' * a * w'⁻¹ * a⁻¹) * w⁻¹) * (w * a * w⁻¹ * a⁻¹) := by group
    rw [e]
    exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp hwE _).mp (hw' a ha)) (hw a ha)
  inv_mem' := by
    rintro w ⟨hwA, hwE, hw⟩
    refine ⟨Subgroup.inv_mem _ hwA, Subgroup.inv_mem _ hwE, fun a ha => ?_⟩
    have ha' : w⁻¹ * a * w ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwA) a).mp ha
      simpa using this
    have e : w⁻¹ * a * w⁻¹⁻¹ * a⁻¹ = (w * (w⁻¹ * a * w) * w⁻¹ * (w⁻¹ * a * w)⁻¹)⁻¹ := by group
    rw [e]
    exact E.inv_mem (hw _ ha')

theorem ggMem_actTrivMod_of_centralizer {A E J : Subgroup G} (hA : A = J ⊔ E)
    (hAE : A ≤ Subgroup.normalizer (E : Set G)) {b : G}
    (hbA : b ∈ Subgroup.normalizer (A : Set G)) (hbE : b ∈ Subgroup.normalizer (E : Set G))
    (hbJ : ∀ j ∈ J, b * j = j * b) : b ∈ ggActTrivMod A E := by
  refine ⟨hbA, hbE, ?_⟩
  let S : Subgroup G :=
    { carrier := {a | a ∈ A ∧ b * a * b⁻¹ * a⁻¹ ∈ E}
      one_mem' := ⟨A.one_mem, by simpa using E.one_mem⟩
      mul_mem' := by
        rintro a a' ⟨ha, hba⟩ ⟨ha', hba'⟩
        refine ⟨A.mul_mem ha ha', ?_⟩
        have e : b * (a * a') * b⁻¹ * (a * a')⁻¹ =
            (b * a * b⁻¹ * a⁻¹) * (a * (b * a' * b⁻¹ * a'⁻¹) * a⁻¹) := by group
        rw [e]
        exact E.mul_mem hba ((Subgroup.mem_normalizer_iff.mp (hAE ha) _).mp hba')
      inv_mem' := by
        rintro a ⟨ha, hba⟩
        refine ⟨A.inv_mem ha, ?_⟩
        have e : b * a⁻¹ * b⁻¹ * a⁻¹⁻¹ = a⁻¹ * (b * a * b⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hAE (A.inv_mem ha)) _).mp (E.inv_mem hba) }
  have hJS : J ≤ S := fun j hj => ⟨by rw [hA]; exact Subgroup.mem_sup_left hj, by
    have : b * j * b⁻¹ * j⁻¹ = 1 := by rw [hbJ j hj]; group
    rw [this]
    exact E.one_mem⟩
  have hES : E ≤ S := fun ε hε => ⟨by rw [hA]; exact Subgroup.mem_sup_right hε,
    E.mul_mem ((Subgroup.mem_normalizer_iff.mp hbE ε).mp hε) (E.inv_mem hε)⟩
  intro a ha
  have : a ∈ S := (sup_le hJS hES) (by rw [← hA]; exact ha)
  exact this.2

theorem ggActTrivMod_conj {A E : Subgroup G} {b y : G} (hb : b ∈ ggActTrivMod A E)
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hyE : y ∈ Subgroup.normalizer (E : Set G)) :
    y⁻¹ * b * y ∈ ggActTrivMod A E := by
  obtain ⟨hbA, hbE, hb⟩ := hb
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyA) hbA) hyA,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyE) hbE) hyE, fun a ha => ?_⟩
  have ha₁ : y * a * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hyA a).mp ha
  have h1 := hb _ ha₁
  have h2 : y⁻¹ * (b * (y * a * y⁻¹) * b⁻¹ * (y * a * y⁻¹)⁻¹) * y⁻¹⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyE) _).mp h1
  have e : y⁻¹ * b * y * a * (y⁻¹ * b * y)⁻¹ * a⁻¹ =
      y⁻¹ * (b * (y * a * y⁻¹) * b⁻¹ * (y * a * y⁻¹)⁻¹) * y⁻¹⁻¹ := by group
  rw [e]
  exact h2

theorem ggComm_of_pComponent_aux [Finite G] {A E J P : Subgroup G} {y b v : G} (hA : A = J ⊔ E)
    (hAE : A ≤ Subgroup.normalizer (E : Set G)) (hEodd : Odd (Nat.card E)) (hP : IsPGroup 2 P)
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hyE : y ∈ Subgroup.normalizer (E : Set G))
    (hbA : b ∈ Subgroup.normalizer (A : Set G)) (hbE : b ∈ Subgroup.normalizer (E : Set G))
    (hbJ : ∀ j ∈ J, b * j = j * b) (hyP : y ∈ P) (hbyb : b * y * b⁻¹ ∈ P) (hvJ : v ∈ J)
    (hvP : v ∈ Subgroup.normalizer (P : Set G)) :
    v * (y⁻¹ * (b * y * b⁻¹)) * v⁻¹ * (y⁻¹ * (b * y * b⁻¹))⁻¹ = 1 := by
  set g := y⁻¹ * (b * y * b⁻¹) with hg
  have hbT : b ∈ ggActTrivMod A E := ggMem_actTrivMod_of_centralizer hA hAE hbA hbE hbJ
  have hgT : g ∈ ggActTrivMod A E := by
    have h1 := ggActTrivMod_conj hbT hyA hyE
    have h2 : (y⁻¹ * b * y) * b⁻¹ ∈ ggActTrivMod A E :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hbT)
    have e : g = (y⁻¹ * b * y) * b⁻¹ := by rw [hg]; group
    rw [e]
    exact h2
  have hvA : v ∈ A := by rw [hA]; exact Subgroup.mem_sup_left hvJ
  have hgP : g ∈ P := P.mul_mem (P.inv_mem hyP) hbyb
  have hwP : v * g * v⁻¹ * g⁻¹ ∈ P :=
    P.mul_mem ((Subgroup.mem_normalizer_iff.mp hvP g).mp hgP) (P.inv_mem hgP)
  have hwE : v * g * v⁻¹ * g⁻¹ ∈ E := by
    have h1 := hgT.2.2 v hvA
    have e : v * g * v⁻¹ * g⁻¹ = (g * v * g⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact E.inv_mem h1
  exact ggEq_one_of_mem_isPGroup_of_mem_odd hP hEodd hwP hwE

theorem ggComm_of_component [Finite G] (hK3 : GGOutTwoCommInner) {K V Ye : Subgroup G}
    {r b y v : G} (hmk : LargeEvenMarking ↥K (fun _ _ _ _ _ _ => True))
    (hZK : Odd (Nat.card (Subgroup.center ↥K))) (hr : r ∈ K) (hr2 : r ^ 2 = 1) (hr1 : r ≠ 1)
    (hV : Nat.card V = 4) (hrV : r ∈ V) (hVK : V ≤ K)
    (hK2 : pCoreOf 2 (K ⊓ Subgroup.centralizer {r}) ≤ Subgroup.normalizer (V : Set G))
    (hYe2 : IsPGroup 2 Ye) (hYeK : Ye ≤ Subgroup.normalizer (K : Set G))
    (hYer : Ye ≤ Subgroup.centralizer {r})
    (hKY : K ⊓ Subgroup.centralizer {r} ≤ Subgroup.normalizer (Ye : Set G))
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    (hbY : b ∈ Subgroup.normalizer (Ye : Set G)) (hy : y ∈ Ye) (hv : v ∈ V) :
    v * (y⁻¹ * (b * y * b⁻¹)) * v⁻¹ * (y⁻¹ * (b * y * b⁻¹))⁻¹ ∈ Subgroup.zpowers r := by
  set g := y⁻¹ * (b * y * b⁻¹) with hg
  set C := Subgroup.centralizer (K : Set G) with hC
  have hbyb : b * y * b⁻¹ ∈ Ye := (Subgroup.mem_normalizer_iff.mp hbY y).mp hy
  have hgYe : g ∈ Ye := Ye.mul_mem (Ye.inv_mem hy) hbyb
  obtain ⟨k, hk, c, hc, hkc⟩ := ggOutTwoComm_apply hK3 hmk hYe2 hYeK (Subgroup.inv_mem _ hbK)
    (by rw [orderOf_inv]; exact hbodd) (Subgroup.inv_mem _ hbY) hy
  have hgkc : g = k * c := by rw [hg, ← hkc]; group
  have hgKC : g ∈ K ⊔ C := by rw [hgkc]; exact Subgroup.mul_mem_sup hk hc
  set Y' : Subgroup G := Ye ⊓ (K ⊔ C) with hY'
  have hgY' : g ∈ Y' := Subgroup.mem_inf.mpr ⟨hgYe, hgKC⟩
  have hY'2 : IsPGroup 2 Y' := hYe2.to_le inf_le_left
  have hN : Subgroup.normalizer (Subgroup.zpowers r : Set G) = Subgroup.centralizer {r} :=
    ggNormalizer_zpowers_eq_centralizer_of_sq hr2 hr1
  have hsup := ggLe_pCoreOf_sup_centralizer_of_le_sup (K := K) (R := Subgroup.zpowers r) (Y := Y')
    (Subgroup.zpowers_le.mpr hr) hY'2 (by rw [hN]; exact inf_le_left.trans hYer)
    (fun n hn => by
      rw [hN] at hn
      exact ggMemNormalizerInf (hKY hn) (Subgroup.le_normalizer (Subgroup.mem_sup_left hn.1)))
    hZK inf_le_right hgY'
  rw [hN] at hsup
  have hKC : K ≤ Subgroup.normalizer (C : Set G) := fun k hk =>
    mem_normalizer_centralizer (Subgroup.le_normalizer hk)
  set Q := pCoreOf 2 (K ⊓ Subgroup.centralizer {r}) with hQ
  have hQK : Q ≤ K := (Subgroup.map_subtype_le _).trans inf_le_left
  have hsup' : g ∈ ((Q ⊔ C : Subgroup G) : Set G) := hsup
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q C (hQK.trans hKC)] at hsup'
  obtain ⟨k', hk', c', hc', hgk'c'⟩ := hsup'
  have hk'r : k' * r = r * k' :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp ((Subgroup.map_subtype_le _) hk' :
        k' ∈ K ⊓ Subgroup.centralizer {r})).2
  have hcv : c' * v⁻¹ * c'⁻¹ = v⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hc' v⁻¹ (K.inv_mem (hVK hv))
    rw [← this]
    group
  have e : v * g * v⁻¹ * g⁻¹ = v * k' * v⁻¹ * k'⁻¹ := by
    rw [← hgk'c']
    calc v * (k' * c') * v⁻¹ * (k' * c')⁻¹ = v * k' * (c' * v⁻¹ * c'⁻¹) * k'⁻¹ := by group
      _ = v * k' * v⁻¹ * k'⁻¹ := by rw [hcv]
  rw [e]
  exact ggCommutator_mem_zpowers_of_card_four hV hr2 hrV hr1 (hK2 hk') hk'r hv

theorem ggFixed_mem_commModR [Finite G] {V J P Y₁ : Subgroup G} {r : G} (hr2 : r ^ 2 = 1)
    (hrJ : r ∈ J) (hP : IsPGroup 2 P) (hZ : Odd (Nat.card (Subgroup.center ↥J))) (hVJ : V ≤ J)
    (hVP : ∀ v ∈ V, v ∈ Subgroup.normalizer (P : Set G)) (hY₁P : Y₁ ≤ P)
    (hY₁J : Y₁ ≤ Subgroup.normalizer (J : Set G)) (hY₁r : Y₁ ≤ Subgroup.centralizer {r})
    (hK1 : ∀ v ∈ V, ∀ y ∈ Y₁, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set G),
      v * y * v⁻¹ * y⁻¹ = r ^ k * z) : Y₁ ≤ ggCommModR V r := by
  intro y hy
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mp (hY₁r hy), fun v hv => ?_⟩
  obtain ⟨k, z, hz, hkz⟩ := hK1 v hv y hy
  have hvJ : v ∈ J := hVJ hv
  have hwJ : v * y * v⁻¹ * y⁻¹ ∈ J := by
    have h1 : y * v⁻¹ * y⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hY₁J hy) v⁻¹).mp (J.inv_mem hvJ)
    have e : v * y * v⁻¹ * y⁻¹ = v * (y * v⁻¹ * y⁻¹) := by group
    rw [e]
    exact J.mul_mem hvJ h1
  have hwP : v * y * v⁻¹ * y⁻¹ ∈ P := by
    have h1 : v * y * v⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hVP v hv) y).mp (hY₁P hy)
    exact P.mul_mem h1 (P.inv_mem (hY₁P hy))
  exact ggMem_zpowers_of_isPGroup_two_of_odd_center hrJ hr2 hP hwP hwJ hz hkz hZ

theorem ggCommutator_le_zpowers_of_pieces [Finite G] {p : ℕ} [Fact p.Prime] {D Y V : Subgroup G}
    {r : G} (hp2 : p ≠ 2) (hD : IsPGroup p D) (hY : IsPGroup 2 Y)
    (hDY : D ≤ Subgroup.normalizer (Y : Set G)) (hDr : D ≤ Subgroup.centralizer {r})
    (hYr : Y ≤ Subgroup.centralizer {r})
    (hfix : ∀ y ∈ Y, (∀ b ∈ D, b * y * b⁻¹ = y) →
      ∀ v ∈ V, v * y * v⁻¹ * y⁻¹ ∈ Subgroup.zpowers r)
    (hcom : ∀ b ∈ D, ∀ y ∈ Y, ∀ v ∈ V,
      v * (y⁻¹ * (b * y * b⁻¹)) * v⁻¹ * (y⁻¹ * (b * y * b⁻¹))⁻¹ ∈ Subgroup.zpowers r) :
    ⁅V, Y⁆ ≤ Subgroup.zpowers r := by
  have hT : Y ≤ ggCommModR V r :=
    ggLe_of_fixed_of_commutators hp2 hD hY hDY
      (fun y hy hfx => ⟨Subgroup.mem_centralizer_singleton_iff.mp (hYr hy), hfix y hy hfx⟩)
      (fun b hb y hy => ⟨Subgroup.mem_centralizer_singleton_iff.mp
        ((Subgroup.centralizer {r}).mul_mem (Subgroup.inv_mem _ (hYr hy))
          ((Subgroup.centralizer {r}).mul_mem
            ((Subgroup.centralizer {r}).mul_mem (hDr hb) (hYr hy))
            (Subgroup.inv_mem _ (hDr hb)))), hcom b hb y hy⟩)
  rw [Subgroup.commutator_le]
  intro v hv y hy
  rw [commutatorElement_def]
  exact (hT hy).2 v hv

end Pieces

end CFSG.StandardType
