module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31c
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs4

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 Equiv
open scoped IsMulCommutative

variable {G : Type} [Group G]

section Star

variable {H : Subgroup G}

theorem isPGroup_star {X : Subgroup G} (hX : IsPGroup 2 X) (hXH : X ≤ H) :
    IsPGroup 2 (star H X) :=
  (hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm).map _

theorem star_le_normalizer_star {X Y : Subgroup G} (hXH : X ≤ H) (hYH : Y ≤ H)
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) :
    star H Y ≤ Subgroup.normalizer (star H X : Set (HStar H)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨y * x * y⁻¹, ?_, by simp⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx hy ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hYX hy) x).1 hx
  · rintro ⟨x, hx, hxz⟩
    refine ⟨y⁻¹ * x * y, ?_, ?_⟩
    · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx hy ⊢
      have := (Subgroup.mem_normalizer_iff.1 (hYX (Y.inv_mem hy)) x).1 hx
      simpa [mul_assoc] using this
    · have : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) x = (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) y *
          z * ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)) y)⁻¹ := hxz
      rw [map_mul, map_mul, map_inv, this]
      group

end Star


section CaseThree

variable [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V] {H K : Subgroup G}

theorem inf_star_M_eq_borel_normal (h1229 : Lemma12_6_29)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hHK : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) :
    star H (Subgroup.normalizer (L : Set G) ⊓ H) ⊓ star H K =
      borel (star H K) (star H T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  have hsylT := isSylowTwoOf_T h
  have hsylTs := isSylowTwoOf_star hsylT
  set Ks := star H K with hKs
  set Ts := star H T with hTs
  set Ms := star H (Subgroup.normalizer (L : Set G) ⊓ H) with hMs
  have hKsn : Ks.Normal := normal_star hKn
  have hTsN : Ts ≤ Subgroup.normalizer (Ks : Set (HStar H)) := Subgroup.le_normalizer_of_normal
  have hSs : QuasithinUnique.IsSylowTwoOf (Ts ⊓ Ks) Ks :=
    A4.isSylowTwoOf_inf_normal hsylTs le_top Subgroup.le_normalizer_of_normal
  have hQM : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) :=
    (pCoreOf_le_of_isSylowTwoOf hsylT).trans hH.hyp.normalizes
  have hBM : borel Ks Ts ≤ Ms := le_sup_right.trans (le_star_M h1229 F hH hZ hTH
    (pCoreOf_ne_bot h) le_sup_left (isSolvable_sup_borel hsylTs.2.1 hTsN hSs))
  refine le_antisymm ?_ (le_inf hBM inf_le_left)
  have hKM : ¬ Ks ≤ Ms := not_le_star_M (le_of_mem_cComp h918.K_cComp) hQM hHK.2.1
  rcases eq_or_eq_of_le_normalizer e₁ hSs (Z := Ms ⊓ Ks) (le_inf hBM inf_le_left)
      inf_le_right with h1 | h1
  · exact h1.le
  · exact absurd (inf_eq_right.1 h1) hKM

theorem not_27_dvd_card_normalizer (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ¬ 27 ∣ Nat.card ↥(Subgroup.normalizer (L : Set G)) := by
  intro h27
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := ↥(Subgroup.normalizer (L : Set G))) 3 (n := 3) (by simpa using h27)
  set P' := P.map (Subgroup.normalizer (L : Set G)).subtype with hP'
  have hP'c : Nat.card P' = 27 := by
    rw [hP', Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP]
    norm_num
  have hPL : P' ≤ L := by
    rw [← S126L1a.part5 h1222 h1228 hH]
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.subset_closure ⟨x.2, 3, ?_⟩
    have := pow_card_eq_one' (G := ↥P) (x := ⟨x, hx⟩)
    rw [hP] at this
    have h1 := congrArg (fun z : ↥P => (z : ↥(Subgroup.normalizer (L : Set G)))) this
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have h27L : 27 ∣ Nat.card L := hP'c ▸ Subgroup.card_dvd_of_le hPL
  have hcard := S126L19a.card_eq F hH (le_refl L)
  obtain ⟨a, ha⟩ := S126L19a.card_inf_eq_pow h1222 hH (le_refl L)
  have hdvd : Nat.card ↥((L.subgroupOf L).map (S126L19a.psi F hH)) ∣ 20160 :=
    S126L1a.card_A8 ▸ Subgroup.card_subgroup_dvd_card _
  rw [hcard, ha] at h27L
  have h27d : 27 ∣ Nat.card ↥((L.subgroupOf L).map (S126L19a.psi F hH)) :=
    (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 27 2)).dvd_of_dvd_mul_right h27L
  have := h27d.trans hdvd
  norm_num at this


theorem case3_of (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (h1229 : Lemma12_6_29)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hHK : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K)
    (hA : Nonempty (↥(star H K) ≃* alternatingGroup (Fin 5))) (hK₀ : conjClosure K T = K) :
    Case3 T L F.V1 H := by
  obtain ⟨e₁⟩ := hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := hK₀ ▸ h918.K₀_normal
  have hHeq : H = K ⊔ (Li L F.V1 ⊔ T) := by
    have := hHK.2.2
    rwa [hK₀] at this
  have hL1TH : Li L F.V1 ⊔ T ≤ H := h.L₁T_le_H
  have hsylT := isSylowTwoOf_T h
  have hsylTs := isSylowTwoOf_star hsylT
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hsylT
  have hR1T : Ri T L F.V1 ≤ T :=
    pCoreOf_le_of_le_normalizer hH.hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  have hQR : pCoreOf 2 H ≤ Ri T L F.V1 :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      (hL1TH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hKM := inf_star_M_eq_borel_normal h1229 F hH hZ hHK h918 hKn e₁
  have hL1TM : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (L : Set G) ⊓ H :=
    le_inf (sup_le (F126.L1_le_L.trans Subgroup.le_normalizer) hH.hyp.normalizes) hL1TH
  set Ks := star H K with hKs
  set Ts := star H T with hTs
  set Ms := star H (Subgroup.normalizer (L : Set G) ⊓ H) with hMs
  set Bs := star H (Li L F.V1 ⊔ T) with hBs
  set Rs := star H (Ri T L F.V1) with hRs
  haveI hKsn : Ks.Normal := normal_star hKn
  have hKM' : Ms ⊓ Ks = Ks ⊓ Subgroup.normalizer ((Ts ⊓ Ks : Subgroup (HStar H)) :
      Set (HStar H)) := hKM
  have hsup : Ks ⊔ Bs = ⊤ := by
    rw [hKs, hBs, ← star_sup hKH hL1TH, ← hHeq, star_self]
  have h27 : ¬ 27 ∣ Nat.card Ms := fun hd =>
    not_27_dvd_card_normalizer h1222 h1228 F hH
      (hd.trans ((Dvd.intro _ (F126.card_star
        (inf_le_right : Subgroup.normalizer (L : Set G) ⊓ H ≤ H))).trans
        (Subgroup.card_dvd_of_le inf_le_left)))
  have h9 : 9 ∣ Nat.card Bs :=
    (F126.nine_dvd_card_star_L1 F hH h).trans (Subgroup.card_dvd_of_le (star_mono le_sup_left))
  have hcop : ∀ (y : HStar H) (n : ℕ), y ^ n = 1 → Nat.Coprime n 6 → y ∈ Ks :=
    fun y n hy hc =>
      mem_star_of_coprime h1222 F hH h.T_normalizes_V₁ hKH hKn hL1TH hHeq hy hc
  have hRn : Bs ≤ Subgroup.normalizer (Rs : Set (HStar H)) :=
    star_le_normalizer_star (hR1T.trans hTH) hL1TH (le_normalizer_pCoreOf 2 _)
  have hRp : IsPGroup 2 Rs := isPGroup_star (pCoreOf_isPGroup 2 _) (hR1T.trans hTH)
  have hRmax : ∀ N : Subgroup (HStar H), N ≤ Bs →
      Bs ≤ Subgroup.normalizer (N : Set (HStar H)) → IsPGroup 2 N → N ≤ Rs := by
    intro N hNB hBN hNp
    set Npre := pre H N ⊓ (Li L F.V1 ⊔ T) with hNpre
    have hNpreN : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (Npre : Set G) :=
      (le_inf (le_normalizer_pre hL1TH hBN) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hNprep : IsPGroup 2 Npre := by
      intro x
      have hx : (x : G) ∈ pre H N := x.2.1
      obtain ⟨hxH, hxN⟩ := mem_pre.1 hx
      obtain ⟨k, hk⟩ := hNp ⟨QuotientGroup.mk ⟨x, hxH⟩, hxN⟩
      have hk' : (QuotientGroup.mk ⟨x, hxH⟩ : HStar H) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hxq : ((x : G) ^ 2 ^ k) ∈ pCoreOf 2 H := by
        have h1 : (QuotientGroup.mk ((⟨x, hxH⟩ : ↥H) ^ 2 ^ k) : HStar H) = 1 := by
          rw [QuotientGroup.mk_pow]; exact hk'
        exact F126.mkH_eq_one_iff.1 h1
      obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨(x : G) ^ 2 ^ k, hxq⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have := congrArg Subtype.val hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [pow_add, pow_mul]
      exact this
    have hNR : Npre ≤ Ri T L F.V1 := le_pCoreOf_of_le_normalizer 2 inf_le_right hNpreN hNprep
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hNB hx
    have hyL : (y : G) ∈ Li L F.V1 ⊔ T := hy
    have hyN : (y : G) ∈ Npre := ⟨mem_pre.2 ⟨y.2, hx⟩, hyL⟩
    exact mk_mem_star (hNR hyN)
  have hRidx : 4 ≤ Rs.relIndex Ts := by
    rw [hRs, hTs, relIndex_star hQR hR1T hTH]
    exact four_le_relIndex h1222 F hH
  obtain ⟨-, hiso, hMs5, hRcore, hRc, hRsq⟩ := case3_abs Ks Ts Ms Bs Rs e₁ hsylTs
    (fun N hn hp => eq_bot_of_isPGroup hn hp) hKM' (star_mono le_sup_right)
    (star_mono hL1TM) hsup h27 h9 hcop (star_mono hR1T) hRn hRp hRmax hRidx
  refine ⟨hiso, ?_, hRcore, hRc, hRsq⟩
  have hQM : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) ⊓ H :=
    le_inf (hQT.trans hH.hyp.normalizes) (pCoreOf_le 2 H)
  rw [← relIndex_star hQM inf_le_right le_rfl, star_self, Subgroup.relIndex_top_right]
  exact hMs5

end CaseThree

end CFSG.Quasithin.H13.S126P31
