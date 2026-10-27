module

public import CFSG.Timmesfeld.ARS.Sec12Basic

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem special_of_commutatorElement_mem [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {X T P : Subgroup G} (hX : X ∈ R) (hT : T ∈ R) (hP : P ∈ R) (hXT : ¬ Commuting X T)
    (hmem : ∀ x ∈ X, ∀ t ∈ T, ⁅x, t⁆ ∈ P) : Special R X T ∧ ⁅X, T⁆ = P := by
  have hne : X ≠ T := fun e => hXT (e ▸ hR.commuting_self hX)
  have hs : Special R X T := by
    rcases hR.rel X hX T hT hne with hc | ho | hs
    · exact absurd hc hXT
    · exfalso
      obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX
      obtain ⟨t, ht, ht1, -⟩ := ho.2.1 x hx hx1
      have hodd := ho.odd_orderOf_mul (hR.mul_self X hX) hx hx1 ht ht1
      have hc : ⁅x, t⁆ = (x * t) ^ 2 := by
        rw [commutatorElement_def, hR.inv_eq hX hx, hR.inv_eq hT ht, sq]
        group
      have h4 : (x * t) ^ 4 = 1 := by
        have h2 := hR.mul_self P hP _ (hmem x hx t ht)
        rw [hc, ← pow_add] at h2
        exact h2
      have hdvd : orderOf (x * t) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
      have h1 : orderOf (x * t) = 1 := by
        have hle : orderOf (x * t) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        obtain ⟨k, hk⟩ := hodd
        interval_cases h : orderOf (x * t)
        all_goals first | rfl | omega
      rw [orderOf_eq_one_iff] at h1
      have hxT : x ∈ X ⊓ T := ⟨hx, by
        rw [eq_inv_of_mul_eq_one_left h1]
        exact T.inv_mem ht⟩
      rw [ho.inf_eq_bot, Subgroup.mem_bot] at hxT
      exact hx1 hxT
    · exact hs
  refine ⟨hs, (QD.eq_of_le_of_mem hR hiso hs.1 hP ?_)⟩
  rw [Subgroup.commutator_le]
  exact hmem

theorem exists_mem_le_sup_commuting (h : Hyp G R) {B X D T : Subgroup G} (hB : B ∈ R)
    (hXB : X ∈ lambdaSet R B) (hD : D ∈ R) (hBD : B ∈ lambdaSet R D)
    (hXD : X ∈ lambdaSet R D) (hT : T ∈ R) (hTD : T ∈ lambdaSet R D)
    (hXT : ¬ Commuting X T) : ∃ Z ∈ R, Z ≤ B ⊔ X ∧ Commuting Z T := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  by_cases hBT : Commuting B T
  · exact ⟨B, hB, le_sup_left, hBT⟩
  have hXR : X ∈ R := hXB.1.1
  have hcommD : ⁅M R D, M R D⁆ = D := (Q_eq_M h hD).2.2.1
  have hMD : IsPGroup 2 ↥(M R D) := (isPGroup_M hR hD).1
  have hTM : T ≤ M R D := QD.le_M hTD
  have hlineM : B ⊔ X ≤ M R D := sup_le (QD.le_M hBD) (QD.le_M hXD)
  have hBTne : B ≠ T := fun e => hBT (e ▸ hR.commuting_self hB)
  have hsBT : Special R B T := by
    rcases hR.rel B hB T hT hBTne with hc | ho | hs
    · exact absurd hc hBT
    · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hB hT
        (hMD.to_le (sup_le (QD.le_M hBD) hTM)))
    · exact hs
  have hBTD : ⁅B, T⁆ = D := QD.eq_of_le_of_mem hR hiso hsBT.1 hD
    (hcommD ▸ Subgroup.commutator_mono (QD.le_M hBD) hTM)
  obtain ⟨t, ht, ht1⟩ := hR.exists_ne_one hT
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hXR
  have hxt : ⁅x, t⁆ ∈ ⁅B, T⁆ := by
    rw [hBTD, ← hcommD]
    exact Subgroup.commutator_mem_commutator (QD.le_M hXD hx) (hTM ht)
  obtain ⟨b, hb, hbt⟩ := (bijOn_commutator_left hR hiso hB hT hsBT ht ht1).surjOn hxt
  replace hbt : ⁅b, t⁆ = ⁅x, t⁆ := hbt
  set y := b * x with hy
  have hyt : ⁅y, t⁆ = 1 := by
    have hxtD : ⁅x, t⁆ ∈ D := hBTD ▸ hxt
    have hcomm : b * ⁅x, t⁆ * b⁻¹ = ⁅x, t⁆ := by
      rw [(hBD.1.2.2 _ hxtD b hb).symm.eq, mul_inv_cancel_right]
    rw [hy, commutatorElement_mul_left_eq_conj_mul, hcomm]
    change ⁅x, t⁆ * ⁅b, t⁆ = 1
    rw [hbt]
    exact hR.mul_self D hD _ hxtD
  have hy1 : y ≠ 1 := by
    intro hy1
    have hxb : x = b⁻¹ := eq_inv_of_mul_eq_one_right hy1
    have hxB : x ∈ B ⊓ X := ⟨hxb ▸ B.inv_mem hb, hx⟩
    rw [inf_eq_bot hR hiso hB hXR hXB.1.2.1.symm, Subgroup.mem_bot] at hxB
    exact hx1 hxB
  have hyle : y ∈ B ⊔ X := Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
    (Subgroup.mem_sup_right hx)
  obtain ⟨Z, hZ, hZle, hyZ⟩ := hXB.2 y hyle hy1
  refine ⟨Z, hZ, hZle, ?_⟩
  have hZT : Z ≠ T := by
    rintro rfl
    exact hBT ((Commuting.sup_right (hR.commuting_self hB) hXB.1.2.2).mono le_rfl hZle)
  rcases hR.rel Z hZ T hT hZT with hc | ho | hs
  · exact hc
  · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hZ hT
      (hMD.to_le (sup_le (hZle.trans hlineM) hTM)))
  · exfalso
    have hinj := (bijOn_commutator hR hiso hZ hT hs hyZ hy1).injOn
    exact ht1 (hinj ht T.one_mem (show ⁅y, t⁆ = ⁅y, 1⁆ by rw [hyt, commutatorElement_one_right]))

theorem not_commuting_and_not_opposite_of_centres [Finite G] (hR : IsRootClass R)
    (hiso : NoIsolated R) {T U D' Z' Y K : Subgroup G} (hU : U ∈ R) (hD' : D' ∈ R) (hZ' : Z' ∈ R) (hD'Z' : D' ≠ Z') (hTZ' : Commuting Z' T)
    (hUZ' : Commuting Z' U) (hDZ : Commuting D' Z') (hsDU : Special R D' U) (hYK : Y ≤ K)
    (hKT : ∀ t ∈ T, conjSub K t = K) (hKU : ∀ u ∈ U, conjSub K u = K) (hKU' : ⁅K, U⁆ ≤ Z')
    (hYT : ⁅Y, T⁆ = D') : ¬ Commuting T U ∧ ¬ Opposite T U := by
  have hex : ∃ y ∈ Y, ∃ t ∈ T, ⁅t, y⁆ ≠ 1 := by
    by_contra hc
    push Not at hc
    apply hR.ne_bot D' hD'
    rw [← hYT, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := hc y hy t ht
    rwa [commutatorElement_eq_one_iff_mul_comm] at this
  obtain ⟨y, hy, t, ht, hty⟩ := hex
  have ht1 : t ≠ 1 := fun e => hty (by rw [e, commutatorElement_one_left])
  have hδ : ⁅t, y⁆ ∈ D' := by
    rw [← hYT, ← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hy ht)
  refine ⟨fun hc => ?_, fun ho => ?_⟩
  · obtain ⟨u, hu, hu1⟩ := hR.exists_ne_one hU
    have hζ : ⁅u, y⁆ ∈ Z' := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (hKU' (Subgroup.commutator_mem_commutator (hYK hy) hu))
    have htu : t * u = u * t := hc t ht u hu
    have htζ : t * ⁅u, y⁆ = ⁅u, y⁆ * t := (hTZ' _ hζ t ht).symm.eq
    have hδζ : ⁅t, y⁆ * ⁅u, y⁆ = ⁅u, y⁆ * ⁅t, y⁆ := hDZ _ hδ _ hζ
    have key : ⁅u, ⁅t, y⁆⁆ = 1 := by
      have e1 : (t * u) * y * (t * u)⁻¹ = ⁅u, y⁆ * ⁅t, y⁆ * y := by
        calc (t * u) * y * (t * u)⁻¹ = t * (⁅u, y⁆ * y) * t⁻¹ := by
              rw [commutatorElement_def]; group
          _ = (t * ⁅u, y⁆) * y * t⁻¹ := by group
          _ = ⁅u, y⁆ * (t * y * t⁻¹) := by rw [htζ]; group
          _ = ⁅u, y⁆ * ⁅t, y⁆ * y := by rw [commutatorElement_def]; group
      have e2 : (u * t) * y * (u * t)⁻¹ = ⁅u, ⁅t, y⁆⁆ * ⁅t, y⁆ * (⁅u, y⁆ * y) := by
        calc (u * t) * y * (u * t)⁻¹ = u * (⁅t, y⁆ * y) * u⁻¹ := by
              rw [commutatorElement_def]; group
          _ = (u * ⁅t, y⁆ * u⁻¹) * (u * y * u⁻¹) := by group
          _ = ⁅u, ⁅t, y⁆⁆ * ⁅t, y⁆ * (⁅u, y⁆ * y) := by
              simp only [commutatorElement_def]; group
      rw [htu, e2, ← mul_assoc, mul_assoc _ ⁅t, y⁆, ← hδζ, ← mul_assoc] at e1
      simpa using e1
    have hinj := (bijOn_commutator hR hiso hD' hU hsDU hδ (fun e => hty e)).injOn
    refine hu1 (hinj hu U.one_mem ?_)
    change ⁅⁅t, y⁆, u⁆ = ⁅⁅t, y⁆, 1⁆
    rw [commutatorElement_one_right, ← commutatorElement_inv, key, inv_one]
  · obtain ⟨u, hu, -, hTu⟩ := ho.2.1 t ht ht1
    have hw : conjSub T (t⁻¹ * u) = U := by
      rw [conjSub_mul, hTu, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have hwK : conjSub K (t⁻¹ * u) = K := by
      rw [conjSub_mul, hKU u hu, hKT _ (T.inv_mem ht)]
    have hwZ : conjSub Z' (t⁻¹ * u) = Z' := conjSub_of_forall_commute fun z hz => by
      have h1 : Commute t⁻¹ z := ((hTZ' z hz t ht).symm).inv_left
      have h2 : Commute u z := (hUZ' z hz u hu).symm
      exact h1.mul_left h2
    have hle : conjSub D' (t⁻¹ * u) ≤ Z' := by
      rw [← hYT, conjSub, Subgroup.map_commutator, ← conjSub, ← conjSub, hw]
      refine le_trans (Subgroup.commutator_mono ?_ le_rfl) hKU'
      rw [← hwK]
      exact Subgroup.map_mono hYK
    have heq := QD.eq_of_le_of_mem hR hiso (hR.conjSub_mem hD' _) hZ' hle
    rw [← hwZ] at heq
    exact hD'Z' (RankOne.map_conj_inj.1 heq)

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem eq_of_le_sup_of_mem_lambdaStar' {P Y : Subgroup G} (hP : P ∈ lambdaStar R A A₀)
    (hY : Y ∈ lambdaStar R A A₀) (hYle : Y ≤ A ⊔ P) : Y = P := by
  have := hS.hyp.finite
  obtain ⟨D', -, hu⟩ := existsUnique_mem_psiSet_of_le hS.hyp.root hS.hyp.noIsolated hS.mem
    hS.opp.1 hS.opp.2 hP.1
  exact (hu Y ⟨hY.1.1.1, hYle, hY.2⟩).trans (hu P ⟨hP.1.1.1, le_sup_right, hP.2⟩).symm

theorem mem_lambdaStar_of_le_sup {P Q Y : Subgroup G} (hP : P ∈ lambdaStar R A A₀)
    (hQ : Q ∈ lambdaStar R A A₀) (hQP : Q ∈ lambdaSet R P) (hY : Y ∈ R) (hYle : Y ≤ P ⊔ Q) :
    Y ∈ lambdaStar R A A₀ := by
  have := hS.hyp.finite
  obtain ⟨F, hF, hPF⟩ := exists_commutator_eq_of_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp
    hP hQ (mem_lambdaSet_comm hP.1.1.1 hQP)
  have hs : Special R P F :=
    special_of_commutator_mem_of_mem_leviSet hS.hyp hS.mem hP hF (hPF ▸ hQ.1.1.1)
  exact (exists_opposite_of_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp hF hP hs).1 Y hY
    (hPF ▸ hYle)

theorem not_le_sup_of_mem_lambdaStar {P Q : Subgroup G} (hP : P ∈ lambdaStar R A A₀)
    (hQ : Q ∈ lambdaStar R A A₀) (hQP : Q ∈ lambdaSet R P) : ¬ A ≤ P ⊔ Q := by
  intro hle
  have := hS.hyp.finite
  have h1 := (mem_lambdaSet_of_le_sup hS.hyp.root hS.hyp.noIsolated hP.1.1.1 hQP hP.1.1.1
    le_sup_left hS.mem hle hP.1.1.2.1).2
  have hQle : Q ≤ A ⊔ P := le_sup_right.trans (h1.symm.le.trans (sup_comm P A).le)
  exact hQP.1.2.1 (hS.eq_of_le_sup_of_mem_lambdaStar' hP hQ hQle)

theorem mem_lambdaSet_of_le_sup' {P Q : Subgroup G} (hP : P ∈ lambdaStar R A A₀)
    (hQ : Q ∈ lambdaStar R A A₀) (hQP : Q ∈ lambdaSet R P) :
    ∀ Y ∈ R, Y ≤ P ⊔ Q → Y ∈ lambdaSet R A :=
  fun _ hY hYle => (hS.mem_lambdaStar_of_le_sup hP hQ hQP hY hYle).1

theorem conjSub_eq_of_le_M {H : Subgroup G} (hAH : A ≤ H) (hHM : H ≤ M R A) {m : G}
    (hm : m ∈ M R A) : conjSub H m = H := by
  have := hS.hyp.finite
  exact conjSub_eq_self_iff.2
    (le_normalizer_of_commutator_le hHM ((Q_eq_M hS.hyp hS.mem).2.2.1.le.trans hAH) hm)

theorem elation_props {P Q T : Subgroup G} (hP : P ∈ lambdaStar R A A₀)
    (hQ : Q ∈ lambdaStar R A A₀) (hQP : Q ∈ lambdaSet R P) (hT : T ∈ R)
    (hTel : Plane.IsElationGroup R (A ⊔ P ⊔ Q) P (P ⊔ A) T) :
    Special R Q T ∧ ⁅Q, T⁆ = P ∧ T ∈ lambdaSet R P ∧ T ∈ sigmaSet R A ∧
      T ∉ lambdaSet R A := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hPR : P ∈ R := hP.1.1.1
  have hQR : Q ∈ R := hQ.1.1.1
  have hQL : ¬ Q ≤ P ⊔ A := fun hle =>
    hQP.1.2.1 (hS.eq_of_le_sup_of_mem_lambdaStar' hP hQ (hle.trans (sup_comm P A).le))
  obtain ⟨P', hP'R, hP'le, hP'Q, hP'P⟩ :=
    exists_mem_le_sup_ne_ne hR hiso hQR (mem_lambdaSet_comm hPR hQP) Q P
  obtain ⟨t, ht, hQt⟩ := hTel.2.2.2 Q hQR le_sup_right hQL P' hP'R hP'le hP'P
  have hQT : ¬ Commuting Q T := fun hc =>
    hP'Q (hQt ▸ conjSub_of_forall_commute fun x hx => (hc x hx t ht).symm)
  obtain ⟨hs, hc⟩ := special_of_commutatorElement_mem hR hiso hQR hT hPR hQT
    fun x hx t ht => hTel.2.1 t ht x ((le_sup_right : Q ≤ A ⊔ P ⊔ Q) hx)
  have hTP : T ∈ lambdaSet R P := by
    have := (mem_lambdaSet_commutator hR hiso hQR hT hs).2
    rwa [hc] at this
  have hAT : Commuting A T := hTel.2.2.1.mono le_sup_right le_rfl
  have hTA : T ≠ A := by
    rintro rfl
    exact hQT hQ.1.1.2.2.symm
  refine ⟨hs, hc, hTP, ⟨hT, hTA, hAT⟩, fun hTl => ?_⟩
  have hle : P ≤ A := by
    rw [← hc, ← (Q_eq_M hS.hyp hS.mem).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M hQ.1) (QD.le_M hTl)
  exact hP.1.1.2.1 (QD.eq_of_le_of_mem hR hiso hPR hS.mem hle)

theorem le_sup_of_mem_lambdaSet {B D X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hD : D ∈ lambdaStar R A A₀) (hX : X ∈ lambdaStar R A A₀) (hDB : D ∈ lambdaSet R B)
    (hXB : X ∈ lambdaSet R B) (hXD : X ∈ lambdaSet R D) : X ≤ B ⊔ D := by
  by_contra hXBD
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hBR : B ∈ R := hB.1.1.1
  have hDR : D ∈ R := hD.1.1.1
  have hXR : X ∈ R := hX.1.1.1
  have hDA : D ≠ A := hD.1.1.2.1
  have hAm : ∀ {m : G}, m ∈ M R A → conjSub A m = A := fun hm =>
    conjSub_eq_self_iff.2 ((isPGroup_M hR hA).2.1 hm)
  have hDBX : ¬ D ≤ B ⊔ X := fun hle => hXBD (le_sup_right.trans
    (mem_lambdaSet_of_le_sup hR hiso hBR hXB hBR le_sup_left hDR hle hDB.1.2.1.symm).2.symm.le)
  obtain ⟨-, -, hel₂⟩ := plane_transitive hR hiso hA hDR hXD
    (hS.mem_lambdaSet_of_le_sup' hD hX hXD)
  obtain ⟨T₂, hT₂R, hT₂⟩ := hel₂ D hDR A hA (le_sup_right.trans le_sup_left)
    (le_sup_left.trans le_sup_left) hDA
  obtain ⟨hsXT₂, hXT₂, hT₂D, hT₂s, hT₂nl⟩ := hS.elation_props hD hX hXD hT₂R hT₂
  have hXT₂c : ¬ Commuting X T₂ := fun hc =>
    hR.ne_bot _ hsXT₂.1 (commuting_iff_commutator_eq_bot.1 hc)
  obtain ⟨Z, hZR, hZle, hZT₂⟩ := exists_mem_le_sup_commuting hS.hyp hBR hXB hDR
    (mem_lambdaSet_comm hBR hDB) hXD hT₂R hT₂D hXT₂c
  have hZ : Z ∈ lambdaStar R A A₀ := hS.mem_lambdaStar_of_le_sup hB hX hXB hZR hZle
  have hZD : Z ≠ D := fun e => hDBX (e ▸ hZle)
  have hZX : Z ≠ X := fun e => hXT₂c (e ▸ hZT₂)
  have hZDl : Z ∈ lambdaSet R D := mem_lambdaSet_of_le_M_of_hyp hS.hyp hDR hZR
    (hZle.trans (sup_le (QD.le_M (mem_lambdaSet_comm hBR hDB)) (QD.le_M hXD))) hZD
  have hZXl : Z ∈ lambdaSet R X := mem_lambdaSet_of_le_M_of_hyp hS.hyp hXR hZR
    (hZle.trans (sup_le (QD.le_M (mem_lambdaSet_comm hBR hXB)) QD.le_M_self)) hZX
  have hDZl : D ∈ lambdaSet R Z := mem_lambdaSet_comm hDR hZDl
  have hlZD := hS.mem_lambdaSet_of_le_sup' hZ hD hDZl
  obtain ⟨hcomm₅, -, -, -, -, -⟩ := plane hR hiso hA hZR hDZl hlZD
  obtain ⟨-, -, hel₅⟩ := plane_transitive hR hiso hA hZR hDZl hlZD
  obtain ⟨T₅, hT₅R, hT₅⟩ := hel₅ Z hZR A hA (le_sup_right.trans le_sup_left)
    (le_sup_left.trans le_sup_left) hZ.1.1.2.1
  obtain ⟨-, hDT₅, hT₅Z, hT₅s, hT₅nl⟩ := hS.elation_props hZ hD hDZl hT₅R hT₅
  obtain ⟨m₂, hm₂, hT₂Δ⟩ :=
    exists_mem_M_conjSub_mem_leviSet hS.hyp hA hS.sec8.2 hS.opp hT₂s hT₂nl
  obtain ⟨m₅, hm₅, hT₅Δ⟩ :=
    exists_mem_M_conjSub_mem_leviSet hS.hyp hA hS.sec8.2 hS.opp hT₅s hT₅nl
  have hline : ∀ {P : Subgroup G}, P ∈ lambdaSet R A → ∀ {m : G}, m ∈ M R A →
      conjSub (A ⊔ P) m = A ⊔ P := fun hP _ hm =>
    hS.conjSub_eq_of_le_M le_sup_left (sup_le QD.le_M_self (QD.le_M hP)) hm
  have hconj_le : ∀ {P : Subgroup G}, P ∈ lambdaSet R A → ∀ {m : G}, m ∈ M R A →
      conjSub P m ≤ A ⊔ P := fun hP _ hm => by
    rw [← hline hP hm]
    exact Subgroup.map_mono le_sup_right
  have hconj_ne : ∀ {P : Subgroup G}, P ≠ A → ∀ {m : G}, m ∈ M R A → conjSub P m ≠ A :=
    fun {P} hPA {m} hm e => hPA (by
      calc P = conjSub (conjSub P m) m⁻¹ := (Plane.conjSub_conjSub_inv P m).symm
        _ = conjSub A m⁻¹ := by rw [e]
        _ = A := hAm ((M R A).inv_mem hm))
  have hsup_eq : ∀ {P P' : Subgroup G}, P ∈ lambdaSet R A → P' ∈ R → P' ≤ A ⊔ P → P' ≠ A →
      A ⊔ P' = A ⊔ P := fun hP hP' hle hne =>
    (mem_lambdaSet_of_le_sup hR hiso hA hP hA le_sup_left hP' hle hne.symm).2
  set D' := conjSub D m₂ with hD'def
  set Z' := conjSub Z m₅ with hZ'def
  set T₂' := conjSub T₂ m₂ with hT₂'def
  set T₅' := conjSub T₅ m₅ with hT₅'def
  have hD'R : D' ∈ R := hR.conjSub_mem hDR m₂
  have hZ'R : Z' ∈ R := hR.conjSub_mem hZR m₅
  have hD'le : D' ≤ A ⊔ D := hconj_le hD.1 hm₂
  have hZ'le : Z' ≤ A ⊔ Z := hconj_le hZ.1 hm₅
  have hD'A : D' ≠ A := hconj_ne hDA hm₂
  have hZ'A : Z' ≠ A := hconj_ne hZ.1.1.2.1 hm₅
  have hcomm_conj : ∀ {P T : Subgroup G}, P ∈ lambdaSet R A → Commuting (A ⊔ P) T →
      ∀ {m : G}, m ∈ M R A → Commuting (A ⊔ P) (conjSub T m) := fun {P T} hP hc {m} hm => by
    have := hc.conjSub m
    rwa [hline hP hm] at this
  have hT₂AD : Commuting (A ⊔ D) T₂ := by
    have := hT₂.2.2.1
    rwa [sup_comm] at this
  have hT₂AZ : Commuting (A ⊔ Z) T₂ :=
    (Commuting.sup_right hT₂s.2.2.symm hZT₂.symm).symm
  have hT₅AZ : Commuting (A ⊔ Z) T₅ := by
    have := hT₅.2.2.1
    rwa [sup_comm] at this
  have hT₂'AD : Commuting (A ⊔ D) T₂' := hcomm_conj hD.1 hT₂AD hm₂
  have hT₂'AZ : Commuting (A ⊔ Z) T₂' := hcomm_conj hZ.1 hT₂AZ hm₂
  have hT₅'AZ : Commuting (A ⊔ Z) T₅' := hcomm_conj hZ.1 hT₅AZ hm₅
  have hD'Z' : D' ≠ Z' := by
    intro e
    have h1 := hsup_eq hD.1 hD'R hD'le hD'A
    have h2 := hsup_eq hZ.1 hZ'R hZ'le hZ'A
    rw [e, h2] at h1
    exact hZD (hS.eq_of_le_sup_of_mem_lambdaStar' hD hZ (h1 ▸ le_sup_right))
  have hZ'Al : Z' ∈ lambdaSet R A :=
    mem_lambdaSet_of_le_M_of_hyp hS.hyp hA hZ'R (hZ'le.trans (sup_le QD.le_M_self
      (QD.le_M hZ.1))) hZ'A
  have hZ'Dl : Z' ∈ lambdaSet R D := by
    refine mem_lambdaSet_of_le_M_of_hyp hS.hyp hDR hZ'R (hZ'le.trans (sup_le
      (QD.le_M (mem_lambdaSet_comm hA hD.1)) (QD.le_M hZDl))) fun e => ?_
    rw [e] at hZ'le
    exact hZD (hS.eq_of_le_sup_of_mem_lambdaStar' hZ hD hZ'le).symm
  have hZ'Xl : Z' ∈ lambdaSet R X := by
    refine mem_lambdaSet_of_le_M_of_hyp hS.hyp hXR hZ'R (hZ'le.trans (sup_le
      (QD.le_M (mem_lambdaSet_comm hA hX.1)) (QD.le_M hZXl))) fun e => ?_
    rw [e] at hZ'le
    exact hZX (hS.eq_of_le_sup_of_mem_lambdaStar' hZ hX hZ'le).symm
  have hAM : A ≤ M R Z' := QD.le_M (mem_lambdaSet_comm hA hZ'Al)
  have hDM : D ≤ M R Z' := QD.le_M (mem_lambdaSet_comm hDR hZ'Dl)
  have hXM : X ≤ M R Z' := QD.le_M (mem_lambdaSet_comm hXR hZ'Xl)
  have hT₅'M : T₅' ≤ M R Z' := QD.le_M (conjSub_mem_lambdaSet hR hT₅Z m₅)
  have hcommZ' : ⁅M R Z', M R Z'⁆ = Z' := (Q_eq_M hS.hyp hZ'R).2.2.1
  have hT₅'A : Commuting A T₅' := by
    have := hT₅s.2.2.conjSub m₅
    rwa [hAm hm₅] at this
  have hD'T₅' : ¬ Commuting D' T₅' := by
    intro hc
    have hc' : Commuting (A ⊔ D) T₅' := by
      rw [← hsup_eq hD.1 hD'R hD'le hD'A]
      exact (Commuting.sup_right hT₅'A.symm hc.symm).symm
    have hc'' := hc'.conjSub m₅⁻¹
    rw [hline hD.1 ((M R A).inv_mem hm₅), hT₅'def, Plane.conjSub_conjSub_inv] at hc''
    exact hR.ne_bot _ (hDT₅ ▸ hZR) (commuting_iff_commutator_eq_bot.1
      (hc''.mono le_sup_right le_rfl))
  have hsD'T₅' : Special R D' T₅' := by
    have hne : D' ≠ T₅' := fun e => hD'T₅' (e ▸ hR.commuting_self hD'R)
    rcases hR.rel D' hD'R T₅' (hR.conjSub_mem hT₅R m₅) hne with hc | ho | hs
    · exact absurd hc hD'T₅'
    · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hD'R (hR.conjSub_mem hT₅R m₅)
        ((isPGroup_M hR hZ'R).1.to_le (sup_le (hD'le.trans (sup_le hAM hDM)) hT₅'M)))
    · exact hs
  obtain ⟨hnc, hno⟩ := not_commuting_and_not_opposite_of_centres hR hiso
    (T := T₂') (K := M R Z') (Y := conjSub X m₂) (hR.conjSub_mem hT₅R m₅) hD'R hZ'R hD'Z'
    (hT₂'AZ.mono hZ'le le_rfl) (hT₅'AZ.mono hZ'le le_rfl)
    (hcomm₅.mono (hD'le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (hZ'le.trans (sup_le (le_sup_left.trans le_sup_left)
        (le_sup_right.trans le_sup_left))))
    hsD'T₅' ((hconj_le hX.1 hm₂).trans (sup_le hAM hXM))
    (fun t ht => (isPGroup_M hR hZ'R).2.2 t (conjSub_eq_self_iff.1
      (conjSub_of_forall_commute fun z hz => (hT₂'AZ.mono hZ'le le_rfl) z hz t ht |>.symm)))
    (fun u hu => conjSub_of_mem (hT₅'M hu))
    ((Subgroup.commutator_mono le_rfl hT₅'M).trans hcommZ'.le)
    (by rw [hT₂'def, conjSub, conjSub, ← Subgroup.map_commutator, hXT₂])
  have hne : T₂' ≠ T₅' := fun e => hnc (e ▸ hR.commuting_self (hR.conjSub_mem hT₅R m₅))
  rcases hR.rel T₂' (hR.conjSub_mem hT₂R m₂) T₅' (hR.conjSub_mem hT₅R m₅) hne with
    hc | ho | hs
  · exact hnc hc
  · exact hno ho
  · exact hS.deg T₂' hT₂Δ T₅' hT₅Δ hs

end Sec12

end CFSG.Timmesfeld.ARS
