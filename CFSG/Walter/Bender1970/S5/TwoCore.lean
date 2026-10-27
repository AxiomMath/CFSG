module

public import CFSG.Walter.Bender1970.S5.Normalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem exists_index_two_not_mem {A : Type*} [Group A] [Finite A]
    (hA : ∀ a b : A, a * b = b * a) (h2 : ∀ a : A, a ^ 2 = 1) {t : A} (ht : t ≠ 1) :
    ∃ B : Subgroup A, B.index = 2 ∧ t ∉ B := by
  classical
  have hnormal : ∀ S : Subgroup A, S.Normal := fun S =>
    ⟨fun n hn g => by rw [hA g n, mul_inv_cancel_right]; exact hn⟩
  have hcard2 : ∀ a : A, a ≠ 1 → Nat.card (Subgroup.zpowers a) = 2 := fun a ha => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h2 a) ha
  have hsmall : ∀ a : A, a ≠ 1 → ∀ S : Subgroup A, a ∉ S → Subgroup.zpowers a ⊓ S = ⊥ := by
    intro a ha S haS
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ S : Subgroup A) ∣ 2 :=
      hcard2 a ha ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : Subgroup.zpowers a ⊓ S = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard2 a ha])
      exact haS ((heq ▸ (inf_le_right : Subgroup.zpowers a ⊓ S ≤ S))
        (heq.symm ▸ Subgroup.mem_zpowers a))
  obtain ⟨B, htB, hBmax⟩ := Set.exists_max_image {B : Subgroup A | t ∉ B} (fun B => Nat.card B)
    (Set.toFinite _) ⟨⊥, fun h => ht (Subgroup.mem_bot.mp h)⟩
  have htB' : t ∉ B := htB
  refine ⟨B, ?_, htB'⟩
  have hC : B ⊔ Subgroup.zpowers t = ⊤ := by
    by_contra hC
    obtain ⟨a, haC⟩ : ∃ a, a ∉ B ⊔ Subgroup.zpowers t := by
      by_contra h
      push Not at h
      exact hC (eq_top_iff.mpr fun x _ => h x)
    have ha1 : a ≠ 1 := fun h => haC (h ▸ one_mem _)
    have haB : a ∉ B := fun h => haC ((le_sup_left : B ≤ B ⊔ Subgroup.zpowers t) h)
    have htB'' : t ∉ B ⊔ Subgroup.zpowers a := by
      intro hmem
      have := hnormal (Subgroup.zpowers a)
      obtain ⟨b, hb, y, hy, hby⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
      have hyC : y ∈ B ⊔ Subgroup.zpowers t := by
        have : y = b⁻¹ * t := by rw [← hby]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hb))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      have hy1 : y = 1 := by
        have h1 : y ∈ Subgroup.zpowers a ⊓ (B ⊔ Subgroup.zpowers t) := ⟨hy, hyC⟩
        rwa [hsmall a ha1 _ haC, Subgroup.mem_bot] at h1
      apply htB'
      rw [← hby, hy1, mul_one]
      exact hb
    have hlt : B < B ⊔ Subgroup.zpowers a :=
      lt_of_le_of_ne le_sup_left fun h => haB (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have := hBmax _ htB''
    exact absurd (Subgroup.card_lt_of_lt hlt) (not_lt.mpr this)
  have hdisj : Disjoint B (Subgroup.zpowers t) := by
    rw [disjoint_iff, inf_comm]
    exact hsmall t ht B htB'
  have hcard := card_sup_eq_mul_of_disjoint_of_le_normalizer B (Subgroup.zpowers t)
    (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr (hnormal B)).ge) hdisj
  rw [hC, Subgroup.card_top, hcard2 t ht] at hcard
  have h := B.card_mul_index
  rw [hcard] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

omit [Finite G] in
theorem eq_one_of_mem_of_isPGroup_of_odd {A B : Subgroup G} (hA : IsPGroup 2 A)
    (hB : Odd (Nat.card B)) {x : G} (hxA : x ∈ A) (hxB : x ∈ B) : x = 1 := by
  obtain ⟨a, ha⟩ := hA ⟨x, hxA⟩
  have h1 : orderOf x ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val ha)
  have h2 : orderOf x ∣ Nat.card B := by
    have := orderOf_dvd_natCard (⟨x, hxB⟩ : B)
    rwa [Subgroup.orderOf_mk] at this
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hB)) h1 h2)

theorem bender1970_5_3
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) :
    (∀ x ∈ qCoreOf H 2, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ H) ∧
      ¬ IsCyclic (qCoreOf H 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hG.isSimpleGroup
  obtain ⟨T, htT⟩ := exists_sylow_two_mem ht
  have hTab := hG.hasAbelianSylowTwo T
  have hHco := isCoatom_of_mem_benderM hH
  have hHA := hG.isAStar_of_isCoatom hHco
  have hHs := bender1970_5_1 hG ht hH
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hE := componentLayerOf_eq_bot_of_isSolvable hHs
  have hO2p : IsPGroup 2 (qCoreOf H 2) := qCoreOf_isPGroup H 2
  have hO2T : qCoreOf H 2 ≤ T := qCoreOf_two_le_sylow T hTH
  refine ⟨fun x hx hx1 => ?_, fun hcyc => ?_⟩
  ·
    obtain ⟨y, hyx, hy⟩ := Bender51.exists_orderOf_eq_two_of_ne_bot
      (hO2p.to_le (Subgroup.zpowers_le.mpr hx))
      (fun h => hx1 (Subgroup.zpowers_eq_bot.mp h))
    have hyO : y ∈ qCoreOf H 2 := Subgroup.zpowers_le.mpr hx hyx
    have hCxy : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyx
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      exact ((Commute.zpow_right (show Commute g x from hg) k)).eq
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hy
      omega
    obtain ⟨M, hM⟩ := hG.benderM_nonempty hy1
    have hNM := bender1970_5_2 hG hy hM T (hO2T hyO)
    have hOy : oddCoreOf H ≤ Subgroup.centralizer ({y} : Set G) := by
      intro d hd
      have hdH : d ∈ H := (oddCoreOf_isNormalIn' H).1 hd
      have hc : y * d * y⁻¹ * d⁻¹ = 1 := by
        refine eq_one_of_mem_of_isPGroup_of_odd hO2p (odd_card_oddCoreOf H) ?_ ?_
        · rw [show y * d * y⁻¹ * d⁻¹ = y * (d * y⁻¹ * d⁻¹) by group]
          exact (qCoreOf H 2).mul_mem hyO ((qCoreOf_normal_in H 2).2 d hdH y⁻¹ (inv_mem hyO))
        · exact (oddCoreOf H).mul_mem ((oddCoreOf_isNormalIn' H).2 y
            ((qCoreOf_normal_in H 2).1 hyO) d hd) (inv_mem hd)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc d * y = (y * d * y⁻¹ * d⁻¹)⁻¹ * (y * d) := by group
        _ = y * d := by rw [hc, inv_one, one_mul]
    have hHM : H ≤ M := le_of_oddCoreOf_le hHA (bender1970_4_3 hG ht hH) T hTH
      (hOy.trans (centralizer_le_of_mem_benderM hM)) (by rw [hE]; exact bot_le)
      (Subgroup.le_normalizer.trans hNM) (inf_le_right.trans hNM)
    have hMH : M = H :=
      ((hHco.le_iff.mp hHM).resolve_left (isCoatom_of_mem_benderM hM).1)
    exact hCxy.trans (hMH ▸ centralizer_le_of_mem_benderM hM)
  ·
    have htO := Bender52.mem_qCoreOf_two hG ht hH
    have hcommT : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
      fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    set A := omegaOneOfComm 2 (T : Subgroup G) hcommT with hAdef
    have hAT : A ≤ T := omegaOneOfComm_le _ hcommT
    have htA : t ∈ A := ⟨htT, by rw [← ht, pow_orderOf_eq_one]⟩
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht
      omega
    obtain ⟨B, hB, htB⟩ := exists_index_two_not_mem (A := A)
      (fun a b => Subtype.ext (hcommT _ (hAT a.2) _ (hAT b.2))) (fun a => Subtype.ext a.2.2)
      (t := ⟨t, htA⟩) (fun h => ht1 (congrArg Subtype.val h))
    have hRT : B.map A.subtype ≤ T := (Subgroup.map_subtype_le B).trans hAT
    obtain ⟨n, hn, hnR⟩ := bender1970_1_3 hG.nonabelian T hTab hRT
      (rank_hyperplane T.isPGroup' hcommT B hB) htT ht
    have hnH := bender1970_5_2 hG ht hH T htT hn
    have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
    have hnt : n * t * n⁻¹ = t := by
      refine eq_of_sq_eq_one_of_isCyclic hcyc ((qCoreOf_normal_in H 2).2 n hnH t htO) htO ?_ ht1
        ?_ ht2
      · intro h
        apply ht1
        calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
          _ = 1 := by rw [h]; group
      · rw [conj_pow, ht2, mul_one, mul_inv_cancel]
    rw [hnt] at hnR
    obtain ⟨b, hb, hbt⟩ := hnR
    apply htB
    have : b = ⟨t, htA⟩ := Subtype.ext hbt
    rw [← this]
    exact hb

end CFSG.Walter
