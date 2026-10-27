module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAuxBase
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.Structure2

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S33

section NoFinite

variable {p : ℕ} {G : Type u} [Group G] {A : Subgroup G} {θ : G → Subgroup G}

theorem thetaStarFun_le (a : G) : thetaStarFun p A θ a ≤ θ a :=
  sup_le (perfRes_le _) inf_le_left

theorem admits_thetaStarFun (hθ : NearFunctor p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Admits A (thetaStarFun p A θ a) :=
  (admits_perfRes (hθ.isFunctor.normalized a ha ha1)).sup
    (Admits.inf (hθ.isFunctor.normalized a ha ha1) (admits_sTwo hθ))

theorem admits_perfRes_inf (a : G) : Admits (θ a ⊓ sTwo p A θ) (perfRes (θ a)) :=
  inf_le_left.trans (admits_perfRes (admits_self (θ a)))

theorem coprime_perfRes_sup (hθ : NearFunctor p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Nat.Coprime p (Nat.card (perfRes (θ a) ⊔ (θ a ⊓ sTwo p A θ) : Subgroup G)) :=
  (hθ.isFunctor.coprime a ha ha1).coprime_dvd_right
    (Subgroup.card_dvd_of_le (sup_le (perfRes_le _) inf_le_left))

theorem cenIn_inf_sTwo_le (hθ : NearFunctor p A θ) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) :
    cenIn (θ a ⊓ sTwo p A θ) {b} ≤ thetaStarFun p A θ b := by
  intro x hx
  obtain ⟨⟨hxa, hxS⟩, hxb⟩ := hx
  have hxb' : x ∈ θ b := hθ.isFunctor.balance a ha ha1 b hb hb1 ⟨hxa, hxb⟩
  exact le_sup_right (a := perfRes (θ b)) ⟨hxb', hxS⟩

end NoFinite

section Balance

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

variable (h : Counterexample p A θ)

include h

theorem cenIn_perfRes_le
    (hθ : NearFunctor p A θ) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) :
    cenIn (perfRes (θ a)) {b} ≤ thetaStarFun p A θ b := by
  have hF := hθ.isFunctor
  have hQ := cenIn_inf_sTwo_le hθ ha ha1 hb hb1
  by_cases hsa : Group.IsSolvable (θ a)
  · have hbot := (perfRes_eq_bot_iff (θ a)).mpr hsa
    intro x hx
    have : x ∈ perfRes (θ a) := hx.1
    rw [hbot, Subgroup.mem_bot] at this
    rw [this]
    exact one_mem _
  · set B : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hBdef
    have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
    have hB1 : B ≠ ⊥ := fun hbot => ha1 (by
      have : Subgroup.zpowers a ≤ ⊥ := hbot ▸ le_sup_left
      exact Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp this))
    have hKB : kOf (θ a) ⊓ Subgroup.centralizer {b} ≤ kOf (thetaOf θ B) :=
      kOf_apply_inf_centralizer_le hθ ha ha1 hb hb1
    have hPK : perfRes (θ a) ≤ kOf (θ a) := h.perfRes_apply_le_kOf ha ha1
    have hP : cenIn (perfRes (θ a)) {b} ≤ kOf (thetaOf θ B) := fun x hx =>
      hKB ⟨hPK hx.1, hx.2⟩
    by_cases hsB : Group.IsSolvable (thetaOf θ B)
    · have hBS : thetaOf θ B ≤ ssol p A θ := h.thetaOf_le_ssol_of_isSolvable hBA hB1 hsB
      have hzR : Subgroup.zpowers a ∈ rSet p A θ := by
        refine h.mem_rSet_iff.mpr ⟨fun hbot => ha1 (Subgroup.zpowers_eq_bot.mp hbot),
          Subgroup.zpowers_le.mpr ha, ?_⟩
        rwa [hF.thetaOf_zpowers ha ha1]
      have h614 := (h.lemma614 hzR).1
      rw [hF.thetaOf_zpowers ha ha1] at h614
      intro x hx
      have hxK : x ∈ kOf (θ a) ⊓ ssol p A θ := ⟨hPK hx.1, hBS (kOf_le _ (hP hx))⟩
      exact hQ ⟨h614 hxK, hx.2⟩
    · have hBR : B ∈ rSet p A θ := h.mem_rSet_iff.mpr ⟨hB1, hBA, hsB⟩
      have hb' : thetaOf θ B ≤ θ b :=
        thetaOf_le_apply (le_sup_right (a := Subgroup.zpowers a) (Subgroup.mem_zpowers b)) hb1
      have hEq := h.perfRes_thetaOf_eq_kOf hB1 hBA hsB
      intro x hx
      have h1 : x ∈ perfRes (thetaOf θ B) := hEq ▸ hP hx
      exact le_sup_left (b := θ b ⊓ sTwo p A θ) (perfRes_mono hb' h1)

theorem balance_thetaStarFun
    {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1) :
    thetaStarFun p A θ a ⊓ Subgroup.centralizer {b} ≤ thetaStarFun p A θ b := by
  have hθ := h.hyp.nearFunctor
  have hcop := coprime_perfRes_sup hθ ha ha1
  have hAP : Admits A (perfRes (θ a)) := admits_perfRes (hθ.isFunctor.normalized a ha ha1)
  have hAQ : Admits A (θ a ⊓ sTwo p A θ) :=
    Admits.inf (hθ.isFunctor.normalized a ha ha1) (admits_sTwo hθ)
  have hsup := cenIn_sup_le_sup hθ.prime hθ.elemAbelian hAP hAQ (admits_perfRes_inf a) hcop hb
  exact fun x hx => (sup_le (cenIn_perfRes_le h hθ ha ha1 hb hb1)
    (cenIn_inf_sTwo_le hθ ha ha1 hb hb1)) (hsup hx)

theorem isFunctor_thetaStarFun :
    IsFunctor p A (thetaStarFun p A θ) := by
  have hθ := h.hyp.nearFunctor
  refine ⟨fun a ha ha1 => (thetaStarFun_le a).trans (hθ.isFunctor.le_centralizer a ha ha1),
    fun a ha ha1 => (hθ.isFunctor.coprime a ha ha1).coprime_dvd_right
      (Subgroup.card_dvd_of_le (thetaStarFun_le a)),
    fun a ha ha1 => admits_thetaStarFun hθ ha ha1, fun a ha ha1 b hb hb1 => ?_⟩
  exact balance_thetaStarFun h ha ha1 hb hb1

theorem nearHyp_thetaStarFun :
    NearHyp p A (thetaStarFun p A θ) where
  prime := h.hyp.prime
  odd := h.hyp.odd
  elemAbelian := h.hyp.elemAbelian
  card := h.hyp.card
  isFunctor := isFunctor_thetaStarFun h
  near := fun a ha ha1 => nearASolvable_of_le h.hyp.prime (h.hyp.near a ha ha1)
    (thetaStarFun_le a) (admits_thetaStarFun h.hyp.nearFunctor ha ha1)

theorem not_isCompleteIn_thetaStarFun :
    ¬ IsCompleteIn (signalizers p A (thetaStarFun p A θ) (NearASolvable p A)) := by
  have hθ := h.hyp.nearFunctor
  rintro ⟨W, hW, hWmax⟩
  obtain ⟨B, hB⟩ := h.rSetN_two_nonempty
  have hle : wsub p A θ ≤ W := by
    rw [← h.lemma64 hB]
    refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
    have hBR := hB.1
    obtain ⟨hB1, hBA, -⟩ := h.mem_rSet_iff.mp hBR
    have hbA : b ∈ A := hBA hb
    have hzR : Subgroup.zpowers b ∈ rSet p A θ :=
      h.rSet_mono hBR (Subgroup.zpowers_le.mpr hb)
        (fun hbot => hb1 (Subgroup.zpowers_eq_bot.mp hbot))
    obtain ⟨hz1, hzA, hzns⟩ := h.mem_rSet_iff.mp hzR
    rw [hθ.isFunctor.thetaOf_zpowers hbA hb1] at hzns
    have hEq := h.perfRes_thetaOf_eq_kOf hz1 hzA (by rwa [hθ.isFunctor.thetaOf_zpowers hbA hb1])
    rw [hθ.isFunctor.thetaOf_zpowers hbA hb1] at hEq
    have hmem : thetaStarFun p A θ b ∈ signalizers p A (thetaStarFun p A θ) (NearASolvable p A) :=
      (isFunctor_thetaStarFun h).apply_mem_signalizers hbA hb1
        (nearASolvable_of_le h.hyp.prime (h.hyp.near b hbA hb1) (thetaStarFun_le b)
          (admits_thetaStarFun hθ hbA hb1))
    calc kOf (θ b) = perfRes (θ b) := hEq.symm
      _ ≤ thetaStarFun p A θ b := le_sup_left
      _ ≤ W := hWmax _ hmem
  have hWassoc : W ∈ assoc p A θ :=
    signalizers_mono_functor (fun a _ _ => thetaStarFun_le a) hW
  exact h.notComplete ⟨W, hWassoc, fun X hX => (le_sSup hX).trans hle⟩

theorem thetaStarFun_eq_apply
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    thetaStarFun p A θ a = θ a := by
  by_contra hne
  have hlt : size A (thetaStarFun p A θ) < size A θ :=
    size_lt_size (fun a _ _ => thetaStarFun_le a) ⟨a, ha, ha1, hne⟩
  exact not_isCompleteIn_thetaStarFun h (h.complete_of_size_lt (nearHyp_thetaStarFun h) hlt)

end Balance

end Sec6S33

end CFSG.SignalizerFunctorTheorem.McBride.Near
