module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLocalSettingFree

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {G : Type*} [Group G] {K : Type} [Field K]

namespace LocalSetting

variable {ω : K} {hω : ω ^ 2 + ω + 1 = 0} {b : G} {L : Subgroup G}
  {φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))} {Bs : Subgroup G}

theorem odd_card_relPPrimeCore [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs) :
    Odd (Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b}))) := by
  classical
  obtain ⟨n, hnN, heL, hnφ⟩ := hS.exists_conj
  set e : G := n * b * n⁻¹ with hedef
  have he3 : orderOf e = 3 := by
    have h := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective b
    simpa [e, MulAut.conj_apply, hS.orderOf_b] using h
  set M : Subgroup G := L.map (MulAut.conj n : G →* G) with hMdef
  have hS' : LocalSetting hω e M (conjEquiv φ n) Bs := hS.conj hnN heL hnφ
  have heBs : e ∈ Bs := by
    have h := (Subgroup.mem_normalizer_iff.mp hnN) b
    exact (h.mp hS.mem)
  have h3U : 3 ∣ Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
    have h1 : 3 ∣ Nat.card (torU K) := by rw [card_torU hS.card_K]; norm_num
    simpa using h1.trans (Subgroup.card_dvd_of_le (H := torU K) (K := ⊤) le_top)
  have h3M : 3 ∣ Nat.card M := by
    rw [hMdef, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    rwa [Nat.card_congr φ.toEquiv]
  have hO2 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {e} →
      ((Q ⊔ relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf
        (Subgroup.centralizer {e})).Normal →
      Q ≤ relPPrimeCore 3 (Subgroup.centralizer {e}) := by
    intro Q hQ2 hQC hQN
    set C : Subgroup G := Subgroup.centralizer {e} with hCdef
    set Oe : Subgroup G := relPPrimeCore 3 C with hOedef
    set N : Subgroup G := Q ⊔ Oe with hNdef
    have hOeC : Oe ≤ C := relPPrimeCore_le (p := 3) C
    have hOeNC : (Oe.subgroupOf C).Normal := relPPrimeCore_normal (p := 3) Nat.prime_three C
    have hNleC : N ≤ C := sup_le hQC hOeC
    have hNnorm : (N.subgroupOf C).Normal := hQN
    have hMnorm : (M.subgroupOf C).Normal := hS'.normal
    have hMsimp : IsSimpleGroup M := isSimpleGroup_L hS'
    have hOeCM : Oe ≤ Subgroup.centralizer (M : Set G) := relPPrimeCore_le_centralizer hS'
    have hMOe : M ⊓ Oe = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxM, hxOe⟩ := Subgroup.mem_inf.mp hx
      have hxc : (⟨x, hxM⟩ : M) ∈ Subgroup.center M := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hOeCM hxOe) y.1 y.2)
      rw [center_L_eq_bot hS'] at hxc
      have h1 : (⟨x, hxM⟩ : M) = 1 := Subgroup.mem_bot.mp hxc
      simpa using congrArg Subtype.val h1
    have hCN : C ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNleC).mp hNnorm
    have hCM : C ≤ Subgroup.normalizer (M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hS'.le_centralizer).mp hMnorm
    have hMN : M ≤ Subgroup.normalizer (N ⊓ M : Subgroup G) :=
      (le_inf (hS'.le_centralizer.trans hCN) Subgroup.le_normalizer).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := N) (K := M))
    have hNMnormal : ((N ⊓ M).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hMN
    haveI := hNMnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top ((N ⊓ M).subgroupOf M) with hbot | htop
    ·
      have hinf : N ⊓ M = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨hxN, hxM⟩ := Subgroup.mem_inf.mp hx
        have hx' : (⟨x, hxM⟩ : M) ∈ (N ⊓ M).subgroupOf M := by
          rw [Subgroup.mem_subgroupOf]; exact ⟨hxN, hxM⟩
        rw [hbot] at hx'
        have h1 : (⟨x, hxM⟩ : M) = 1 := Subgroup.mem_bot.mp hx'
        simpa using congrArg Subtype.val h1
      have hNcent : N ≤ Subgroup.centralizer (M : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hxC : x ∈ C := hNleC hx
        have hyC : y ∈ C := hS'.le_centralizer hy
        have h1 : y * x⁻¹ * y⁻¹ ∈ N :=
          ((Subgroup.mem_normalizer_iff.mp (hCN hyC)) x⁻¹).mp (N.inv_mem hx)
        have h2 : x * (y * x⁻¹ * y⁻¹) ∈ N := N.mul_mem hx h1
        have h3 : x * y * x⁻¹ ∈ M :=
          ((Subgroup.mem_normalizer_iff.mp (hCM hxC)) y).mp hy
        have h4 : x * y * x⁻¹ * y⁻¹ ∈ M := M.mul_mem h3 (M.inv_mem hy)
        have h5 : x * y * x⁻¹ * y⁻¹ ∈ N ⊓ M := by
          refine Subgroup.mem_inf.mpr ⟨?_, h4⟩
          rwa [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) from by group]
        rw [hinf] at h5
        have hone : x * y * x⁻¹ * y⁻¹ = 1 := Subgroup.mem_bot.mp h5
        have h6 : x * y * x⁻¹ = y := by
          have h7 := congrArg (fun z => z * y) hone
          simpa [mul_assoc] using h7
        calc y * x = (x * y * x⁻¹) * x := by rw [h6]
          _ = x * y := by group
      have hNleP : N ≤ Oe ⊔ Subgroup.zpowers e := by
        have hle : N ≤ C ⊓ Subgroup.centralizer (M : Set G) := le_inf hNleC hNcent
        exact (centralizer_inf_eq hS') ▸ hle
      intro q hq
      have hqN : q ∈ N := Subgroup.mem_sup_left hq
      have hqP : q ∈ Oe ⊔ Subgroup.zpowers e := hNleP hqN
      have hPleC : Oe ⊔ Subgroup.zpowers e ≤ C :=
        sup_le hOeC (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      have hCnormOe : C ≤ Subgroup.normalizer (Oe : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hOeC).mp hOeNC
      haveI : (Oe.subgroupOf (Oe ⊔ Subgroup.zpowers e)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (hPleC.trans hCnormOe)
      have hqP' : (⟨q, hqP⟩ : ↥(Oe ⊔ Subgroup.zpowers e)) ∈
          (Oe.subgroupOf (Oe ⊔ Subgroup.zpowers e)) ⊔
            ((Subgroup.zpowers e).subgroupOf (Oe ⊔ Subgroup.zpowers e)) := by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
        exact Subgroup.mem_top _
      obtain ⟨o, ho, p, hp, hop⟩ := Subgroup.mem_sup_of_normal_left.mp hqP'
      have hoOe : (o : G) ∈ Oe := Subgroup.mem_subgroupOf.mp ho
      have hpP : (p : G) ∈ Subgroup.zpowers e := Subgroup.mem_subgroupOf.mp hp
      have hqeq : (o : G) * (p : G) = q := congrArg Subtype.val hop
      have hcomm : Commute (o : G) (p : G) := by
        have hoe : (o : G) * e = e * (o : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp (hOeC hoOe)
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hpP
        rw [← hi]
        exact (show Commute (o : G) e from hoe).zpow_right i
      have hp3 : (p : G) ^ 3 = 1 := by
        have hdvd : orderOf (p : G) ∣ 3 := by
          have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers e) hpP
          rwa [Nat.card_zpowers, he3] at h
        rwa [orderOf_dvd_iff_pow_eq_one] at hdvd
      have hq3 : q ^ 3 ∈ Oe := by
        rw [← hqeq, hcomm.mul_pow, hp3, mul_one]
        exact Oe.pow_mem hoOe 3
      obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
      have hqkC : (⟨q, hQC hq⟩ : C) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        have h := congrArg (fun z : Q => (z : G)) hk
        simpa using h
      have hq1 : QuotientGroup.mk' (Oe.subgroupOf C) ⟨q, hQC hq⟩ = 1 := by
        have hord : orderOf (QuotientGroup.mk' (Oe.subgroupOf C) ⟨q, hQC hq⟩) ∣ 1 := by
          have hgcd : Nat.gcd 3 (2 ^ k) = 1 := by
            have hc : Nat.Coprime 3 (2 ^ k) :=
              ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num)).pow_right k
            exact Nat.coprime_iff_gcd_eq_one.mp hc
          rw [← hgcd]
          refine Nat.dvd_gcd ?_ ?_
          · rw [orderOf_dvd_iff_pow_eq_one, ← map_pow]
            exact (QuotientGroup.eq_one_iff _).mpr
              (by rw [Subgroup.mem_subgroupOf]; simpa using hq3)
          · rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hqkC]
            exact map_one _
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq1)
    ·
      exfalso
      have hMleN : M ≤ N := by
        intro x hx
        have hx' : (⟨x, hx⟩ : M) ∈ (N ⊓ M).subgroupOf M := by
          rw [htop]; exact Subgroup.mem_top _
        exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx')).1
      set mk := QuotientGroup.mk' (Oe.subgroupOf C) with hmkdef
      have hOe_ker : Oe.subgroupOf C ≤ MonoidHom.ker mk := by
        intro x hx
        rw [MonoidHom.mem_ker]
        exact (QuotientGroup.eq_one_iff x).mpr hx
      have hNc : (N.subgroupOf C).map mk = (Q.subgroupOf C).map mk := by
        have h1 : N.subgroupOf C = (Q.subgroupOf C) ⊔ (Oe.subgroupOf C) := by
          rw [← Subgroup.subgroupOf_sup hQC hOeC]
        rw [h1, Subgroup.map_sup, Subgroup.map_eq_bot_iff _ |>.mpr hOe_ker, sup_bot_eq]
      have hQc2 : IsPGroup 2 (Q.subgroupOf C) :=
        hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
      have hle : (M.subgroupOf C).map mk ≤ (N.subgroupOf C).map mk :=
        Subgroup.map_mono (Subgroup.subgroupOf_mono C hMleN)
      have hMc2 : IsPGroup 2 ((M.subgroupOf C).map mk) :=
        (hQc2.map mk).to_le (hNc ▸ hle)
      have hxeM : n * e * n⁻¹ ∈ M := by
        have h : (MulAut.conj n : G →* G) e ∈ M := by
          rw [hMdef]; exact Subgroup.mem_map_of_mem (MulAut.conj n : G →* G) heL
        simpa [MulAut.conj_apply] using h
      have hxe3 : orderOf (n * e * n⁻¹) = 3 := by
        have h := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective e
        simpa [MulAut.conj_apply, he3] using h
      have hxeOe : n * e * n⁻¹ ∉ Oe := by
        intro hxOe
        have h3dvd : 3 ∣ Nat.card Oe := by
          have h := Subgroup.orderOf_dvd_natCard Oe hxOe
          rwa [hxe3] at h
        have hcop : Nat.Coprime 3 (Nat.card Oe) :=
          coprime_card_relPPrimeCore (p := 3) Nat.prime_three C
        have h1 : 3 ∣ Nat.gcd 3 (Nat.card Oe) := Nat.dvd_gcd dvd_rfl h3dvd
        rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at h1
        norm_num at h1
      have hxmem : mk (⟨n * e * n⁻¹, hS'.le_centralizer hxeM⟩ : C) ∈
          (M.subgroupOf C).map mk :=
        Subgroup.mem_map_of_mem mk (by rw [Subgroup.mem_subgroupOf]; exact hxeM)
      have hord3 : orderOf (mk ⟨n * e * n⁻¹, hS'.le_centralizer hxeM⟩) = 3 := by
        have hdvd : orderOf (mk ⟨n * e * n⁻¹, hS'.le_centralizer hxeM⟩) ∣ 3 := by
          have h1 := orderOf_map_dvd mk (⟨n * e * n⁻¹, hS'.le_centralizer hxeM⟩ : C)
          rwa [Subgroup.orderOf_mk, hxe3] at h1
        have hne : mk ⟨n * e * n⁻¹, hS'.le_centralizer hxeM⟩ ≠ 1 := by
          intro h1
          apply hxeOe
          have h2 := (QuotientGroup.eq_one_iff (N := Oe.subgroupOf C)
            ⟨n * e * n⁻¹, hS'.le_centralizer hxeM⟩).mp h1
          exact Subgroup.mem_subgroupOf.mp h2
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hne
        · exact h1
      have h3dvd : 3 ∣ Nat.card ((M.subgroupOf C).map mk) := by
        have h := Subgroup.orderOf_dvd_natCard ((M.subgroupOf C).map mk) hxmem
        rwa [hord3] at h
      have h2pow : ∃ j, Nat.card ((M.subgroupOf C).map mk) = 2 ^ j :=
        IsPGroup.iff_card.mp hMc2
      obtain ⟨j, hj⟩ := h2pow
      rw [hj] at h3dvd
      have h3j : ¬ 3 ∣ 2 ^ j := by
        intro hd
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
      exact h3j h3dvd
  refine odd_card_of_le_centralizer_threeA (L := L) hG hS.card_K hω φ.toMonoidHom
    φ.surjective ?_ he3 heL ⟨1, by simp [e, hnφ]⟩ hO2 ?_
    (relPPrimeCore_le_centralizer_and_odd_index hS').1 ?_
    (relPPrimeCore_le_centralizer_and_odd_index hS).1 ?_ (relPPrimeCore_le_centralizer hS)
  · rw [(MonoidHom.ker_eq_bot_iff φ.toMonoidHom).mpr φ.injective, Subgroup.card_bot]
    norm_num
  ·
    refine Subgroup.centralizer_le ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact heBs
  ·
    exact (relPPrimeCore_le_centralizer_and_odd_index hS').2
  ·
    exact (relPPrimeCore_le_centralizer_and_odd_index hS).2

theorem odd_card_centralizer_inf_centralizer [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs) :
    Odd (Nat.card (Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G) : Subgroup G)) := by
  classical
  rw [centralizer_inf_eq hS]
  have hRcard : Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b}) ⊔ Subgroup.zpowers b :
        Subgroup G) =
      Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b})) * 3 := by
    have hOleCb : relPPrimeCore 3 (Subgroup.centralizer {b}) ≤
        Subgroup.centralizer ({b} : Set G) := relPPrimeCore_le _
    haveI : ((relPPrimeCore 3 (Subgroup.centralizer {b})).subgroupOf
        (relPPrimeCore 3 (Subgroup.centralizer {b}) ⊔ Subgroup.zpowers b)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        ((sup_le hOleCb (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr rfl))).trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hOleCb).mp
            (relPPrimeCore_normal (p := 3) Nat.prime_three _)))
    have hdisj : relPPrimeCore 3 (Subgroup.centralizer {b}) ⊓ Subgroup.zpowers b = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxO, hxb⟩ := Subgroup.mem_inf.mp hx
      have h2 : orderOf x ∣ 3 := by
        have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers b) hxb
        rwa [Nat.card_zpowers, hS.orderOf_b] at h
      have hodd : Odd (orderOf x) :=
        (odd_card_relPPrimeCore hG hS).of_dvd_nat
          (Subgroup.orderOf_dvd_natCard (relPPrimeCore 3 (Subgroup.centralizer {b})) hxO)
      rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        have h3 : 3 ∣ Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b})) :=
          h ▸ Subgroup.orderOf_dvd_natCard (relPPrimeCore 3 (Subgroup.centralizer {b})) hxO
        have hcop3 : Nat.Coprime 3
            (Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b}))) :=
          coprime_card_relPPrimeCore (p := 3) Nat.prime_three _
        have h1 : 3 ∣ Nat.gcd 3
            (Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b}))) :=
          Nat.dvd_gcd dvd_rfl h3
        rw [Nat.coprime_iff_gcd_eq_one.mp hcop3] at h1
        norm_num at h1
    let f : ↥(relPPrimeCore 3 (Subgroup.centralizer {b})) × ↥(Subgroup.zpowers b) →
        ↥(relPPrimeCore 3 (Subgroup.centralizer {b}) ⊔ Subgroup.zpowers b) := fun z =>
      ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩
    have hinj : Function.Injective f := by
      rintro ⟨o1, p1⟩ ⟨o2, p2⟩ h
      simp only [f, Subtype.mk.injEq] at h
      have hmemO : (o1 : G)⁻¹ * o2 ∈ relPPrimeCore 3 (Subgroup.centralizer {b}) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ o1.2) o2.2
      have hmemP : (p1 : G) * (p2 : G)⁻¹ ∈ Subgroup.zpowers b :=
        Subgroup.mul_mem _ p1.2 (Subgroup.inv_mem _ p2.2)
      have heq : (p1 : G) * (p2 : G)⁻¹ = (o1 : G)⁻¹ * o2 := by
        have h' := congrArg (fun z : G => (o1 : G)⁻¹ * z * (p2 : G)⁻¹) h
        simpa [mul_assoc] using h'
      have hmem : (o1 : G)⁻¹ * o2 ∈
          relPPrimeCore 3 (Subgroup.centralizer {b}) ⊓ Subgroup.zpowers b :=
        ⟨hmemO, by rw [← heq]; exact hmemP⟩
      rw [hdisj] at hmem
      have hone : (o1 : G)⁻¹ * o2 = 1 := Subgroup.mem_bot.mp hmem
      have ho : (o1 : G) = o2 := by
        have h := congrArg (fun y : G => (o1 : G) * y) hone
        simpa [mul_assoc] using h.symm
      have hp : (p1 : G) = p2 := by
        have hb1 : (p1 : G) * (p2 : G)⁻¹ = 1 := by rw [heq, hone]
        have h := congrArg (fun y : G => y * (p2 : G)) hb1
        simpa [mul_assoc] using h
      exact Prod.ext (Subtype.ext ho) (Subtype.ext hp)
    have hsurj : Function.Surjective f := by
      intro x
      have hx' : x ∈ (relPPrimeCore 3 (Subgroup.centralizer {b})).subgroupOf
          (relPPrimeCore 3 (Subgroup.centralizer {b}) ⊔ Subgroup.zpowers b) ⊔
          (Subgroup.zpowers b).subgroupOf
            (relPPrimeCore 3 (Subgroup.centralizer {b}) ⊔ Subgroup.zpowers b) := by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
        exact Subgroup.mem_top _
      obtain ⟨o, ho, p, hp, hop⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
      refine ⟨(⟨(o : G), Subgroup.mem_subgroupOf.mp ho⟩,
        ⟨(p : G), Subgroup.mem_subgroupOf.mp hp⟩), ?_⟩
      exact Subtype.ext (congrArg Subtype.val hop)
    calc Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b}) ⊔ Subgroup.zpowers b : Subgroup G)
        = Nat.card (↥(relPPrimeCore 3 (Subgroup.centralizer {b})) ×
            ↥(Subgroup.zpowers b)) :=
          Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
      _ = Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b})) *
            Nat.card (Subgroup.zpowers b) := Nat.card_prod _ _
      _ = Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b})) * 3 := by
          rw [Nat.card_zpowers, hS.orderOf_b]
  rw [hRcard]
  exact (odd_card_relPPrimeCore hG hS).mul (by norm_num : Odd 3)

theorem exists_involution [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs) {g : G} (hgB : ∀ y ∈ Bs ⊓ L, g * y * g⁻¹ = y)
    (hgb : g * b * g⁻¹ = b⁻¹) :
    ∃ t ∈ Subgroup.zpowers g, t ∈ Subgroup.normalizer (Bs : Set G) ∧ orderOf t = 2 ∧
      t * b * t⁻¹ = b⁻¹ ∧ t ∈ Subgroup.centralizer (L : Set G) := by
  classical
  haveI hLsimple : IsSimpleGroup L := isSimpleGroup_L hS
  have hbne : b ≠ b⁻¹ := by
    intro h
    have h2 : b ^ 2 = 1 := by
      have h3 := congrArg (fun z => z * b) h
      simpa [pow_two] using h3
    have hd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hS.orderOf_b] at hd
    norm_num at hd
  have commute_of_conj : ∀ {a c : G}, a * c * a⁻¹ = c → Commute a c := by
    intro a c h
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [h]
  have hgbP : ∀ p ∈ Subgroup.zpowers b, g * p * g⁻¹ ∈ Subgroup.zpowers b := by
    intro p hp
    have hmap : (Subgroup.zpowers b).map (MulAut.conj g : G →* G) = Subgroup.zpowers b := by
      have h := CFSG.GroupTheory.map_conj_zpowers g b
      rw [hgb, Subgroup.zpowers_inv] at h
      exact h
    rw [← hmap]
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj g : G →* G) hp
  have hgN : g ∈ Subgroup.normalizer (Bs : Set G) := by
    apply CFSG.GroupTheory.mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨p, hp, y, hy, rfl⟩ := exists_mul_eq_of_mem_Bs hS hx
    have h1 : g * p * g⁻¹ ∈ Subgroup.zpowers b := hgbP p hp
    have h2 : g * y * g⁻¹ ∈ Bs ⊓ L := by
      rw [hgB y hy]
      exact hy
    have h3 : g * (p * y) * g⁻¹ = (g * p * g⁻¹) * (g * y * g⁻¹) := by group
    rw [h3]
    exact Bs.mul_mem (Subgroup.zpowers_le.mpr hS.mem h1) h2.1
  have hg2b : g ^ 2 * b * (g ^ 2)⁻¹ = b := by
    rw [pow_two, mul_inv_rev]
    calc g * g * b * (g⁻¹ * g⁻¹) = g * (g * b * g⁻¹) * g⁻¹ := by group
      _ = g * b⁻¹ * g⁻¹ := by rw [hgb]
      _ = (g * b * g⁻¹)⁻¹ := by group
      _ = (b⁻¹)⁻¹ := by rw [hgb]
      _ = b := inv_inv b
  have hcommg2 : Commute (g ^ 2) b := commute_of_conj hg2b
  have hg2C : g ^ 2 ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨p, hp, y, hy, rfl⟩ := exists_mul_eq_of_mem_Bs hS hx
    have hp' : Commute (g ^ 2) p := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
      rw [← hk]
      exact hcommg2.zpow_right k
    have h2 : g ^ 2 * y * (g ^ 2)⁻¹ = y := by
      rw [pow_two, mul_inv_rev]
      calc g * g * y * (g⁻¹ * g⁻¹) = g * (g * y * g⁻¹) * g⁻¹ := by group
        _ = g * y * g⁻¹ := by conv_lhs => rw [hgB y hy]
        _ = y := hgB y hy
    have hy' : Commute (g ^ 2) y := commute_of_conj h2
    exact (hp'.mul_right hy').symm
  obtain ⟨a, m, hm_odd, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  set t : G := g ^ m with htdef
  have hmpos : 0 < m := hm_odd.pos
  have hmdvd : m ∣ orderOf g := by
    rw [hN]
    exact dvd_mul_left m (2 ^ a)
  have htord : orderOf t = 2 ^ a := by
    rw [htdef, orderOf_pow, Nat.gcd_eq_right hmdvd, hN, Nat.mul_div_cancel _ hmpos]
  have hgpow : ∀ y ∈ Bs ⊓ L, ∀ k : ℕ, g ^ k * y * (g ^ k)⁻¹ = y := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc g ^ k * g * y * (g ^ k * g)⁻¹
          = g ^ k * (g * y * g⁻¹) * (g ^ k)⁻¹ := by group
        _ = g ^ k * y * (g ^ k)⁻¹ := by rw [hgB y hy]
        _ = y := ih
  have htB : ∀ y ∈ Bs ⊓ L, t * y * t⁻¹ = y := by
    intro y hy
    rw [htdef]
    exact hgpow y hy m
  have hfix2 : ∀ j : ℕ, g ^ (2 * j) * b * (g ^ (2 * j))⁻¹ = b := by
    intro j
    have h1 : g ^ (2 * j) = (g ^ 2) ^ j := pow_mul g 2 j
    rw [h1, (hcommg2.pow_left j).eq]
    group
  have htinv : t * b * t⁻¹ = b⁻¹ := by
    obtain ⟨j, hj⟩ := hm_odd
    rw [htdef, hj, pow_succ]
    have step : g ^ (2 * j) * g * b * (g ^ (2 * j) * g)⁻¹
        = g ^ (2 * j) * (g * b * g⁻¹) * (g ^ (2 * j))⁻¹ := by group
    rw [step, hgb]
    have h1 : g ^ (2 * j) = (g ^ 2) ^ j := pow_mul g 2 j
    rw [h1, (hcommg2.pow_left j).inv_right.eq]
    group
  have ht2C : t ^ 2 ∈ Subgroup.centralizer (Bs : Set G) := by
    have heq : t ^ 2 = (g ^ 2) ^ m := by
      rw [htdef, ← pow_mul, mul_comm m 2, pow_mul]
    rw [heq]
    exact Subgroup.pow_mem _ hg2C m
  have hCodd : Odd (Nat.card (Subgroup.centralizer (Bs : Set G))) := by
    obtain ⟨hOle, hidx⟩ := relPPrimeCore_le_centralizer_and_odd_index hS
    have hcard : Nat.card (Subgroup.centralizer (Bs : Set G)) =
        Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b})) *
          ((relPPrimeCore 3 (Subgroup.centralizer {b})).subgroupOf
            (Subgroup.centralizer (Bs : Set G))).index := by
      have h1 := Subgroup.card_mul_index
        (H := (relPPrimeCore 3 (Subgroup.centralizer {b})).subgroupOf
          (Subgroup.centralizer (Bs : Set G)))
      have h2 : Nat.card ↥((relPPrimeCore 3 (Subgroup.centralizer {b})).subgroupOf
          (Subgroup.centralizer (Bs : Set G))) =
          Nat.card (relPPrimeCore 3 (Subgroup.centralizer {b})) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOle).toEquiv
      rw [h2] at h1
      exact h1.symm
    rw [hcard]
    exact (odd_card_relPPrimeCore hG hS).mul (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx))
  have hcop : Nat.Coprime (2 ^ a) (Nat.card (Subgroup.centralizer (Bs : Set G))) :=
    (Nat.coprime_two_left.mpr hCodd).pow_left a
  have ht2 : t ^ 2 = 1 := by
    have hdvd1 : orderOf (t ^ 2) ∣ 2 ^ a := by
      rw [← htord, orderOf_dvd_iff_pow_eq_one, ← pow_mul, mul_comm 2 (orderOf t),
        pow_mul, pow_orderOf_eq_one, one_pow]
    have hdvd2 : orderOf (t ^ 2) ∣ Nat.card (Subgroup.centralizer (Bs : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ ht2C
    have hone : orderOf (t ^ 2) = 1 := by
      have hg : orderOf (t ^ 2) ∣
          Nat.gcd (2 ^ a) (Nat.card (Subgroup.centralizer (Bs : Set G))) :=
        Nat.dvd_gcd hdvd1 hdvd2
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hg
      exact Nat.dvd_one.mp hg
    rwa [orderOf_eq_one_iff] at hone
  have htne : t ≠ 1 := by
    intro h1
    have h2 : t * b * t⁻¹ = b := by rw [h1]; group
    rw [htinv] at h2
    exact hbne h2.symm
  have htord2 : orderOf t = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime ht2 htne
  have htNBs : t ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [htdef]
    exact Subgroup.pow_mem _ hgN m
  have hCbN : t ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G)) := by
    apply CFSG.GroupTheory.mem_normalizer_of_conj_mem
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hinv : t⁻¹ * b * t = b⁻¹ := by
      have h : b = t⁻¹ * b⁻¹ * t := by
        have h' := congrArg (fun z => t⁻¹ * z * t) htinv
        simpa [mul_assoc] using h'
      calc t⁻¹ * b * t = (t⁻¹ * b⁻¹ * t)⁻¹ := by group
        _ = b⁻¹ := by rw [← h]
    have hxb' : x * b⁻¹ = b⁻¹ * x := (show Commute x b from hx).inv_right.eq
    have hbt : t * b⁻¹ * t⁻¹ = b := by
      have h : t * b⁻¹ * t⁻¹ = (t * b * t⁻¹)⁻¹ := by group
      rw [h, htinv, inv_inv]
    calc t * x * t⁻¹ * b = t * (x * (t⁻¹ * b * t)) * t⁻¹ := by group
      _ = t * (x * b⁻¹) * t⁻¹ := by rw [hinv]
      _ = t * (b⁻¹ * x) * t⁻¹ := by rw [hxb']
      _ = (t * b⁻¹ * t⁻¹) * (t * x * t⁻¹) := by group
      _ = b * (t * x * t⁻¹) := by rw [hbt]
  have hCbNleL : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS.le_centralizer).mp hS.normal
  set L' : Subgroup G := L.map (MulAut.conj t : G →* G) with hL'def
  have hL'Cb : L' ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [hL'def]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyC : y ∈ Subgroup.centralizer ({b} : Set G) := hS.le_centralizer hy
    have h2 : t * y * t⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hCbN y).mp hyC
    simpa [MulAut.conj_apply] using h2
  have hconjL : ∀ y ∈ Subgroup.centralizer ({b} : Set G), ∀ x ∈ L, y * x * y⁻¹ ∈ L := by
    intro y hy x hx
    exact (Subgroup.mem_normalizer_iff.mp (hCbNleL hy) x).mp hx
  have hconjL' : ∀ y ∈ Subgroup.centralizer ({b} : Set G), ∀ x ∈ L', y * x * y⁻¹ ∈ L' := by
    intro y hy x hx
    rw [hL'def] at hx ⊢
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    have hyt : t⁻¹ * y * t ∈ Subgroup.centralizer ({b} : Set G) :=
      (Subgroup.mem_normalizer_iff''.mp hCbN y).mp hy
    have key : (t⁻¹ * y * t) * l * (t⁻¹ * y * t)⁻¹ ∈ L := hconjL _ hyt l hl
    have h2 : (MulAut.conj t : G →* G) ((t⁻¹ * y * t) * l * (t⁻¹ * y * t)⁻¹)
        = y * ((MulAut.conj t : G →* G) l) * y⁻¹ := by
      show t * ((t⁻¹ * y * t) * l * (t⁻¹ * y * t)⁻¹) * t⁻¹ = y * (t * l * t⁻¹) * y⁻¹
      group
    rw [← h2]
    exact Subgroup.mem_map_of_mem (MulAut.conj t : G →* G) key
  have hL'infL_normal : ((L ⊓ L').subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    exact ⟨hconjL k (hS.le_centralizer hk) h hh.1,
      hconjL' k (hS.le_centralizer hk) h hh.2⟩
  have hRodd := odd_card_centralizer_inf_centralizer hG hS
  have h2L : 2 ∣ Nat.card L := by
    rw [Nat.card_congr φ.toEquiv]
    change 2 ∣ Nat.card (StatedProj (StatedSU 6 (2 ^ 1) K))
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (p := 2) (f := 1) (n := 6)
      Nat.prime_two le_rfl ?_ (by norm_num)]
    · decide
    · rw [hS.card_K]; norm_num
  have htNL : t ∈ Subgroup.normalizer (L : Set G) := by
    by_contra hnot
    have hne : L' ≠ L := by
      intro h
      rw [hL'def] at h
      exact hnot (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    haveI : ((L ⊓ L').subgroupOf L).Normal := hL'infL_normal
    rcases Subgroup.Normal.eq_bot_or_eq_top ((L ⊓ L').subgroupOf L) with hbot | htop
    · have hinf : L ⊓ L' = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨hxL, hxL'⟩ := Subgroup.mem_inf.mp hx
        have hx' : (⟨x, hxL⟩ : L) ∈ (L ⊓ L').subgroupOf L := by
          rw [Subgroup.mem_subgroupOf]; exact ⟨hxL, hxL'⟩
        rw [hbot] at hx'
        have h1 : (⟨x, hxL⟩ : L) = 1 := Subgroup.mem_bot.mp hx'
        simpa using congrArg Subtype.val h1
      have hL'leCL : L' ≤ Subgroup.centralizer (L : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyCb : y ∈ Subgroup.centralizer ({b} : Set G) := hS.le_centralizer hy
        have hxCb : x ∈ Subgroup.centralizer ({b} : Set G) := hL'Cb hx
        have h1 : x * y⁻¹ * x⁻¹ ∈ L := hconjL x hxCb y⁻¹ (L.inv_mem hy)
        have h2 : y * (x * y⁻¹ * x⁻¹) ∈ L := L.mul_mem hy h1
        have h3 : y * x * y⁻¹ ∈ L' := hconjL' y hyCb x hx
        have h4 : y * x * y⁻¹ * x⁻¹ ∈ L' := L'.mul_mem h3 (L'.inv_mem hx)
        have h5 : y * x * y⁻¹ * x⁻¹ ∈ L ⊓ L' := by
          refine Subgroup.mem_inf.mpr ⟨?_, h4⟩
          rwa [show y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) from by group]
        rw [hinf] at h5
        have hone : y * x * y⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp h5
        have h6 : y * x * y⁻¹ = x := by
          have h := congrArg (fun z => z * x) hone
          simpa [mul_assoc] using h
        exact (calc x * y = (y * x * y⁻¹) * y := by rw [h6]
          _ = y * x := by group).symm
      have hL'leR : L' ≤ Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L : Set G) :=
        le_inf hL'Cb hL'leCL
      have h2L' : 2 ∣ Nat.card L' := by
        rw [hL'def, Subgroup.card_map_of_injective (MulAut.conj t).injective]
        exact h2L
      have h2R : 2 ∣ Nat.card (Subgroup.centralizer {b} ⊓
          Subgroup.centralizer (L : Set G) : Subgroup G) :=
        h2L'.trans (Subgroup.card_dvd_of_le hL'leR)
      exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h2R)
    · have hle : L ≤ L ⊓ L' := Subgroup.subgroupOf_eq_top.mp htop
      have heq : L = L' := Subgroup.eq_of_le_of_card_ge (hle.trans inf_le_right)
        (by rw [hL'def, Subgroup.card_map_of_injective (MulAut.conj t).injective])
      exact hne heq.symm
  have hfix : ∀ u ∈ torU K, inducedAut hS t htNL u = u :=
    inducedAut_apply_of_mem_torU hS htNL htB
  have hα3 : inducedAut hS t htNL ^ 3 = 1 :=
    pow_three_eq_one_of_forall_fix_torU hS.card_K _ hfix
  have hα2 : inducedAut hS t htNL ^ 2 = 1 := by
    rw [inducedAut_pow hS htNL 2]
    ext u
    obtain ⟨x, rfl⟩ := φ.surjective u
    rw [inducedAut_apply, MulAut.one_apply, φ.injective.eq_iff]
    apply Subtype.ext
    show (t ^ 2) * (x : G) * (t ^ 2)⁻¹ = (x : G)
    rw [ht2]
    group
  have hα1 : inducedAut hS t htNL = 1 := by
    have h : inducedAut hS t htNL ^ 2 * inducedAut hS t htNL = 1 := by
      rw [← pow_succ]
      exact hα3
    rw [hα2, one_mul] at h
    exact h
  have htCL : t ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := congrArg (fun α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =>
      α (φ ⟨x, hx⟩)) hα1
    rw [inducedAut_apply, MulAut.one_apply] at h
    have h' : (⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp htNL x).mp hx⟩ : L) =
        ⟨x, hx⟩ := φ.injective (by simpa using h)
    have hval : t * x * t⁻¹ = x := congrArg Subtype.val h'
    calc x * t = (t * x * t⁻¹) * t := by rw [hval]
      _ = t * x := by group
  have htzp : t ∈ Subgroup.zpowers g := by
    rw [htdef]
    exact Subgroup.pow_mem (Subgroup.zpowers g) (Subgroup.mem_zpowers g) m
  exact ⟨t, htzp, htNBs, htord2, htinv, htCL⟩

end LocalSetting

end CFSG.StandardType.USixTwo

end
