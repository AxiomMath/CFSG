module

public import CFSG.Quasithin.Vol2.Ch7Sec77Cen
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem coe_mem_pCoreOf {K : Subgroup G} {x : ↥K} (hx : x ∈ CFSG.pCore 2 ↥K) :
    (x : G) ∈ pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff x).mpr hx

theorem eq_top_of_index_le_five {K : Subgroup G} (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : 120 < (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)).index)
    (h2 : ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup 2 (↥K ⧸ N) → N = ⊤)
    {N : Subgroup ↥K} (hN : N.index ≤ 5) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCrN : N.normalCore ≤ N := Subgroup.normalCore_le N
  have hCi : N.normalCore.index ≤ 120 :=
    (Subgroup.index_normalCore_le_factorial_index N).trans
      ((Nat.factorial_le hN).trans (by decide))
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hnorm : (N.normalCore.map π).Normal := Subgroup.Normal.map inferInstance π hπs
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hKq
      (N.normalCore.map π) with hc | ht
  · exfalso
    have h1 := (Subgroup.index_dvd_of_le hc).trans (Subgroup.index_map_dvd (H := N.normalCore) hπs)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
    omega
  · have hCr : N.normalCore = ⊤ := by
      refine h2 N.normalCore ?_
      set f : ↥(CFSG.pCore 2 ↥K) →* ↥K ⧸ N.normalCore :=
        (QuotientGroup.mk' N.normalCore).comp (CFSG.pCore 2 ↥K).subtype with hf
      have hfs : Function.Surjective f := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        have hx : π x ∈ N.normalCore.map π := by rw [ht]; exact Subgroup.mem_top _
        obtain ⟨c, hc, hcx⟩ := hx
        have hp : c⁻¹ * x ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq).mp hcx
        refine ⟨⟨_, hp⟩, ?_⟩
        rw [hf, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
          QuotientGroup.eq]
        have e : (c⁻¹ * x)⁻¹ * x = x⁻¹ * c * x := by group
        rw [e]
        have h1 := (inferInstance : N.normalCore.Normal).conj_mem c hc x⁻¹
        rwa [inv_inv] at h1
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).of_surjective f hfs
    exact eq_top_iff.mpr (hCr ▸ hCrN)

theorem mem_of_mem_normalizer_of_index_fifteen {K B : Subgroup G}
    (hOB : pCoreOf 2 K ≤ B) (hB : (B.subgroupOf K).index = 15)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : 120 < (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)).index)
    (h2 : ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup 2 (↥K ⧸ N) → N = ⊤)
    {x : G} (hxK : x ∈ K) (hxN : x ∈ Subgroup.normalizer (B : Set G)) : x ∈ B := by
  set N := (Subgroup.normalizer (B : Set G)).subgroupOf K with hNdef
  set B' := B.subgroupOf K with hB'
  have hBN : B' ≤ N := fun b hb => Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp hb)
  have hmul := Subgroup.relIndex_mul_index hBN
  rw [hB] at hmul
  have hdvd : N.index ∣ 15 := Dvd.intro_left _ hmul
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNt : N ≠ ⊤ := by
    intro htop
    have hBn : B'.Normal := by
      refine ⟨fun b hb k => ?_⟩
      have hk : (k : G) ∈ Subgroup.normalizer (B : Set G) := by
        have : k ∈ N := by rw [htop]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hk _).mp
        (Subgroup.mem_subgroupOf.mp hb))
    have hnorm : (B'.map π).Normal := Subgroup.Normal.map hBn π hπs
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hKq (B'.map π) with
      hc | ht
    · have h1 := (Subgroup.index_dvd_of_le hc).trans (Subgroup.index_map_dvd (H := B') hπs)
      rw [hB] at h1
      have := Nat.le_of_dvd (by norm_num) h1
      omega
    · have hBt : B' = ⊤ := by
        rw [eq_top_iff]
        intro k _
        have hk : π k ∈ B'.map π := by rw [ht]; exact Subgroup.mem_top _
        obtain ⟨b, hb, hbk⟩ := hk
        have hp : b⁻¹ * k ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq).mp hbk
        have h1 : ((b⁻¹ * k : ↥K) : G) ∈ B := hOB (coe_mem_pCoreOf hp)
        have h2 : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
        have e : (k : G) = b * ((b⁻¹ * k : ↥K) : G) := by simp
        rw [Subgroup.mem_subgroupOf, e]
        exact B.mul_mem h2 h1
      rw [hBt, Subgroup.index_top] at hB
      omega
  have hN15 : N.index = 15 := by
    have hmem : N.index ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h15 : Nat.divisors 15 = {1, 3, 5, 15} := by decide
    rw [h15] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact absurd (Subgroup.index_eq_one.mp h) hNt
    · exact absurd (eq_top_of_index_le_five hKq hZ h2 (by omega)) hNt
    · exact absurd (eq_top_of_index_le_five hKq hZ h2 (by omega)) hNt
    · exact h
  have hrel : B'.relIndex N = 1 := by rw [hN15] at hmul; omega
  have hNB : N ≤ B' := Subgroup.relIndex_eq_one.mp hrel
  have hxN' : (⟨x, hxK⟩ : ↥K) ∈ N := Subgroup.mem_subgroupOf.mpr hxN
  exact Subgroup.mem_subgroupOf.mp (hNB hxN')

omit [Finite G] in
theorem mem_normalizer_of_central {K B : Subgroup G} (hBK : B ≤ K) (hOB : pCoreOf 2 K ≤ B)
    {z : G} (hzK : z ∈ K) (hz : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ pCoreOf 2 K) :
    z ∈ Subgroup.normalizer (B : Set G) := by
  have key : ∀ w ∈ K, (∀ k ∈ K, k * w * k⁻¹ * w⁻¹ ∈ pCoreOf 2 K) →
      ∀ y ∈ B, w * y * w⁻¹ ∈ B := by
    intro w hwK hw y hy
    have h1 : w * y * w⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
      have h2 := hw y (hBK hy)
      have e : w * y * w⁻¹ * y⁻¹ = (y * w * y⁻¹ * w⁻¹)⁻¹ := by group
      rw [e]
      exact (pCoreOf 2 K).inv_mem h2
    have e : w * y * w⁻¹ = (w * y * w⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact B.mul_mem (hOB h1) hy
  have hzinv : ∀ k ∈ K, k * z⁻¹ * k⁻¹ * z⁻¹⁻¹ ∈ pCoreOf 2 K := by
    intro k hk
    have hN : z⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      le_normalizer_pCoreOf 2 K (K.inv_mem hzK)
    have h1 := (Subgroup.mem_normalizer_iff.mp hN _).mp ((pCoreOf 2 K).inv_mem (hz k hk))
    have e : k * z⁻¹ * k⁻¹ * z⁻¹⁻¹ = z⁻¹ * (k * z * k⁻¹ * z⁻¹)⁻¹ * z⁻¹⁻¹ := by group
    rw [e]
    exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key z hzK hz y, fun h => ?_⟩
  have h1 := key z⁻¹ (K.inv_mem hzK) hzinv _ h
  have e : z⁻¹ * (z * y * z⁻¹) * z⁻¹⁻¹ = y := by group
  rwa [e] at h1

omit [Finite G] in
theorem mem_oTwoZIn_of_commutator_mem {K : Subgroup G}
    (hperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K)) {c : G} (hcK : c ∈ K)
    (h : ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ oTwoZIn K) : c ∈ oTwoZIn K := by
  set X := ↥K ⧸ CFSG.pCore 2 ↥K with hX
  have hmemZ : ∀ y : ↥K, (y : G) ∈ oTwoZIn K →
      (QuotientGroup.mk y : X) ∈ Subgroup.center X := by
    intro y hy
    unfold oTwoZIn preimageModTwoCore at hy
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp hy
    have e : y' = y := Subtype.ext hyy'
    rw [← e]
    exact hy'
  set ρ := QuotientGroup.mk' (Subgroup.center X) with hρ
  have hρc : ρ (QuotientGroup.mk ⟨c, hcK⟩) ∈ Subgroup.center (X ⧸ Subgroup.center X) := by
    refine Subgroup.mem_center_iff.mpr fun w => ?_
    obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w'
    have h1 := hmemZ (⟨c, hcK⟩ * x * (⟨c, hcK⟩ : ↥K)⁻¹ * x⁻¹) (h x x.2)
    have h2 : ρ (QuotientGroup.mk (⟨c, hcK⟩ * x * (⟨c, hcK⟩ : ↥K)⁻¹ * x⁻¹)) = 1 := by
      rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv] at h2
    have e : ρ (QuotientGroup.mk x) * ρ (QuotientGroup.mk ⟨c, hcK⟩) =
        (ρ (QuotientGroup.mk ⟨c, hcK⟩) * ρ (QuotientGroup.mk x) *
          (ρ (QuotientGroup.mk ⟨c, hcK⟩))⁻¹ * (ρ (QuotientGroup.mk x))⁻¹)⁻¹ *
          (ρ (QuotientGroup.mk ⟨c, hcK⟩) * ρ (QuotientGroup.mk x)) := by group
    rw [e, h2, inv_one, one_mul]
  rw [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot, hρ,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hρc
  unfold oTwoZIn preimageModTwoCore
  exact Subgroup.mem_map.mpr ⟨⟨c, hcK⟩, hρc, rfl⟩

theorem eq_one_of_commute_alternating {n : ℕ} (hn : 5 ≤ n) {π : Equiv.Perm (Fin n)}
    (h : ∀ a ∈ alternatingGroup (Fin n), π * a = a * π) : π = 1 := by
  classical
  have key : ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → π i = i ∨ π i = j ∨ π i = k := by
    intro i j k hij hik hjk
    set c := Equiv.swap i k * Equiv.swap i j with hcdef
    have hc : c ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, hcdef, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap hik, Equiv.Perm.sign_swap hij]
      decide
    have hci : c i = j := by
      rw [hcdef, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) hjk]
    have hcomm := congrArg (fun f => f i) (h c hc)
    simp only [Equiv.Perm.mul_apply] at hcomm
    rw [hci] at hcomm
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2, h3⟩ := hne
    have hcfix : c (π i) = π i := by
      rw [hcdef, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2,
        Equiv.swap_apply_of_ne_of_ne h1 h3]
    rw [hcfix] at hcomm
    exact hij (π.injective hcomm).symm
  ext i
  have hcard : 4 ≤ (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.erase i).card)
  have hc1 : 3 ≤ ((Finset.univ.erase i).erase j).card := by
    rw [Finset.card_erase_of_mem hj]; omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase i).erase j).card)
  have hc2 : 2 ≤ (((Finset.univ.erase i).erase j).erase k).card := by
    rw [Finset.card_erase_of_mem hk]; omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp
    (by omega : 0 < (((Finset.univ.erase i).erase j).erase k).card)
  have hc3 : 1 ≤ ((((Finset.univ.erase i).erase j).erase k).erase l).card := by
    rw [Finset.card_erase_of_mem hl]; omega
  obtain ⟨m, hm⟩ := Finset.card_pos.mp
    (by omega : 0 < ((((Finset.univ.erase i).erase j).erase k).erase l).card)
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj hk hl hm
  have h1 := key i j k (Ne.symm hj) (Ne.symm hk.2) (Ne.symm hk.1)
  have h2 := key i l m (Ne.symm hl.2.2) (Ne.symm hm.2.2.2) (Ne.symm hm.1)
  rw [Equiv.Perm.coe_one, id]
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2
  all_goals first
    | exact congrArg Fin.val h1
    | exact congrArg Fin.val h2
    | exact absurd (h1.symm.trans h2) (by tauto)

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem false_of_c27Hat6 (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G) (hF : CharTwo H)
    {K V' : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKM : ¬ K ≤ fsuM T L)
    (h : C27Hat6 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K V') : False := by
  obtain ⟨⟨hshort, ⟨-, h3, ⟨eA⟩⟩, -, -⟩, hidx, -⟩ := h
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hZ : 120 < (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)).index := by
    rw [Subgroup.index, Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card,
      card_alternatingGroup]
    decide
  have hnt : Nontrivial ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, h3]
    norm_num
  obtain ⟨⟨c, hc⟩, hc1⟩ := exists_ne (1 : ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hco : orderOf c = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 : orderOf (⟨c, hc⟩ : ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))) ∣ 3 :=
      h3 ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1'
    · exact h
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨j, hj⟩ := exists_odd_pow (k : G)
  have hzK : (k : G) ^ 2 ^ j ∈ K := K.pow_mem k.2 _
  have hzmk : (QuotientGroup.mk (⟨(k : G) ^ 2 ^ j, hzK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) =
      (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 2 ^ j := by
    rw [← QuotientGroup.mk_pow]
    congr 1
  have hzc : (QuotientGroup.mk (⟨(k : G) ^ 2 ^ j, hzK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      Subgroup.center _ := by
    rw [hzmk]
    exact Subgroup.pow_mem _ hc _
  have hz1' : (QuotientGroup.mk (⟨(k : G) ^ 2 ^ j, hzK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ≠ 1 := by
    rw [hzmk]
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hco] at h1
    have h2 : (3 : ℕ) ∣ 2 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
    omega
  have hz : ∀ x ∈ K, x * (k : G) ^ 2 ^ j * x⁻¹ * ((k : G) ^ 2 ^ j)⁻¹ ∈ pCoreOf 2 K := by
    intro x hx
    have h1 := Subgroup.mem_center_iff.mp hzc (QuotientGroup.mk ⟨x, hx⟩)
    have h2 : (⟨x, hx⟩ * ⟨(k : G) ^ 2 ^ j, hzK⟩ * (⟨x, hx⟩ : ↥K)⁻¹ *
        (⟨(k : G) ^ 2 ^ j, hzK⟩ : ↥K)⁻¹ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, h1]
      group
    exact coe_mem_pCoreOf h2
  have hz1 : (k : G) ^ 2 ^ j ∉ pCoreOf 2 K := by
    rintro ⟨x, hx, hxz⟩
    apply hz1'
    rw [QuotientGroup.eq_one_iff]
    have e : x = ⟨(k : G) ^ 2 ^ j, hzK⟩ := Subtype.ext hxz
    rw [← e]
    exact hx
  have hOB : pCoreOf 2 K ≤ fsuM T L ⊓ H ⊓ K := fun x hx =>
    ⟨⟨C.pCoreOf_le_fsuM hK hx, hKH (pCoreOf_le 2 K hx)⟩, pCoreOf_le 2 K hx⟩
  have hB : ((fsuM T L ⊓ H ⊓ K).subgroupOf K).index = 15 := by
    rw [Subgroup.inf_subgroupOf_right]
    exact hidx
  have hzB := mem_of_mem_normalizer_of_index_fifteen hOB hB hKq hZ hshort.1 hzK
    (mem_normalizer_of_central inf_le_right hOB hzK hz)
  exact C.false_of_central h443 hC24a hF hK hKq hKM hzK hzB.1.1 hj.1 hz1 hz

theorem not_inf_le_pCoreOf_of_hom {K : Subgroup G} (hK : K ∈ cComp H) {Y : Type*} [Group Y]
    (α : ↥K →* Y) (hαk : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → α k = 1)
    (h3 : ∀ X : Subgroup G, IsSylowTwoOf X K → 2 < Nat.card ((X.subgroupOf K).map α)) :
    ¬ T ⊓ Subgroup.centralizer (fsuV T I : Set G) ⊓ K ≤ pCoreOf 2 K := by
  intro hle
  set X := T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K with hXdef
  have hXS : IsSylowTwoOf X K :=
    CFSG.Quasithin.A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) C.conf.sylH
  obtain ⟨R, hRX, hR2, hRQ⟩ := C.exists_index_two_Q (inf_le_left : X ≤ _)
  have h2 : Nat.card ((X.subgroupOf K).map α) ≤ 2 := card_map_le_two α inf_le_right hR2
    fun k hk => hαk k (hle ⟨hRQ hk, (hRX hk).2⟩)
  have := h3 X hXS
  omega

theorem false_of_c27SL3_even (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit')
    (hC24a : ASC24One G) (hC24b : ASC24TwoChar G) (hF : CharTwo H) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L)
    {n : ℕ} {F : Type} [Field F] [Fintype F] (hFc : Fintype.card F = 2 ^ n) (hn : Even n)
    (eF : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
      (fsuV T I : Set G))))) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hP : IsParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
      (fsuV T I : Set G))))) (autOn (fsuM T L ⊓ H ⊓ K) (omegaOneCenterOf (pCoreOf 2
      (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  set V' := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hV'
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hQN := C.Q_le_normalizer h443 hC24a hC24b hF hK hKq hKM
  have hK2 : CharTwo K := CFSG.Quasithin.A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hF
  obtain ⟨⟨h1a, h1b, -⟩, -, -⟩ := hC27 H _ _ K _ C.hypC23 hK hKq hK2
    (fun h => hKM (h.trans inf_le_left)) hQN rfl
  have hKV : K ≤ Subgroup.normalizer (V' : Set G) := le_normalizer_omegaOneCenterOf_sup K Q
  have hKn : (K.subgroupOf (K ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hQN)
  have hOKQ : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ Q) :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 (CFSG.Quasithin.A4.subnormal_of_normal le_sup_left hKn)
  have hOV' : pCoreOf 2 K ≤ Subgroup.centralizer (V' : Set G) := fun x hx => (h1a (hOKQ hx)).2
  have h3 : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hFc]
    obtain ⟨r, rfl⟩ := hn
    have : 2 ^ 2 - 1 ∣ 2 ^ (r + r) - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (m := 2) (k := r + r) ⟨r, by ring⟩
    simpa using this
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hsmem : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈
      CFSG.Assembly.LowTwoRank.StatedSL 3 F := by
    refine Subgroup.subset_closure ?_
    show (((Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) F)) :
      Matrix (Fin 3) (Fin 3) F).det = 1
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
    simpa [Finset.prod_const] using congrArg Units.val hω3
  set s : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) := ⟨_, hsmem⟩ with hs
  have hscomm : ∀ g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F), g * s = s * g := fun g =>
    Subtype.ext (Matrix.GeneralLinearGroup.scalar_commute _ _).symm
  have hs3 : s ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, hs, ← map_pow, hω3, map_one])
  have hs1 : s ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) h
    simp [hs, Matrix.GeneralLinearGroup.coe_scalar] at h1
    rw [h1, orderOf_one] at hω
    omega
  set zs : MulAut ↥V' := ((eF.symm s : ↥(autOn K V')) : MulAut ↥V') with hzs
  have hzsX : zs ∈ autOn K V' := (eF.symm s).2
  have hzcomm : ∀ a ∈ autOn K V', a * zs = zs * a := by
    intro a ha
    have h1 : (⟨a, ha⟩ : ↥(autOn K V')) * eF.symm s = eF.symm s * ⟨a, ha⟩ := by
      apply eF.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hscomm _
    exact congrArg Subtype.val h1
  have hzs1 : zs ≠ 1 := by
    intro h
    apply hs1
    have h1 : eF.symm s = 1 := Subtype.ext h
    rw [← MulEquiv.apply_symm_apply eF s, h1, map_one]
  have hzs3 : zs ^ 3 = 1 := by
    have h1 : (eF.symm s) ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
    have := congrArg Subtype.val h1
    simpa using this
  obtain ⟨-, S', hS', hNS⟩ := hP
  have hzsP : zs ∈ autOn (fsuM T L ⊓ H ⊓ K) V' := by
    refine hNS (Subgroup.mem_inf.mpr ⟨hzsX, ?_⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    by_cases hy : y ∈ autOn K V'
    · rw [← hzcomm y hy, mul_inv_cancel_right]
    · constructor
      · intro h
        exact absurd (hS'.1 h) hy
      · intro h
        exfalso
        apply hy
        have h1 := (autOn K V').mul_mem ((autOn K V').mul_mem ((autOn K V').inv_mem hzsX)
          (hS'.1 h)) hzsX
        simpa [mul_assoc] using h1
  obtain ⟨g, hgMK, hgz⟩ := Setup.mem_autOn_iff.mp hzsP
  have hgK : (g : G) ∈ K := hgMK.2
  have hgZ : (g : G) ∈ oTwoZIn K := by
    refine mem_oTwoZIn_of_commutator_mem hKq.1 hgK fun x hx => ?_
    refine inf_centralizer_le_oTwoZIn_of_c27 h1b ⟨K.mul_mem (K.mul_mem (K.mul_mem hgK hx)
      (K.inv_mem hgK)) (K.inv_mem hx), ?_⟩
    have hxV : x ∈ Subgroup.normalizer (V' : Set G) := hKV hx
    have hmem : (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ Subgroup.normalizer (V' : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hxV)
        (Subgroup.inv_mem _ g.2)) (Subgroup.inv_mem _ hxV)
    have hx' : conjAct V' ⟨x, hxV⟩ ∈ autOn K V' :=
      Setup.mem_autOn_iff.mpr ⟨⟨x, hxV⟩, hx, rfl⟩
    have h1 : conjAct V' ⟨_, hmem⟩ = 1 := by
      have e : (⟨_, hmem⟩ : ↥(Subgroup.normalizer (V' : Set G))) =
          g * ⟨x, hxV⟩ * g⁻¹ * (⟨x, hxV⟩ : ↥(Subgroup.normalizer (V' : Set G)))⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hgz, ← hzcomm _ hx']
      group
    exact (Setup.rho_eq_one_iff (P := Subgroup.normalizer (V' : Set G)) le_rfl ⟨_, hmem⟩).mp h1
  obtain ⟨j, hj⟩ := CFSG.Quasithin.H.BlkW.exists_odd_pow (g : G)
  have hz : ∀ k ∈ K, k * (g : G) * k⁻¹ * (g : G)⁻¹ ∈ pCoreOf 2 K := fun k hk =>
    commutator_mem_of_mem_oTwoZIn hgZ hk
  refine C.false_of_central h443 hC24a hF hK hKq hKM (K.pow_mem hgK _)
    ((fsuM T L).pow_mem hgMK.1.1 _) hj ?_ (fun x hx => conj_pow_mul_inv_mem hgK hz hx _)
  intro hO
  have hC := hOV' hO
  have hpow : ((g ^ 2 ^ j : ↥(Subgroup.normalizer (V' : Set G))) : G) = (g : G) ^ 2 ^ j := by
    simp
  have h1 : conjAct V' (g ^ 2 ^ j) = 1 :=
    (Setup.rho_eq_one_iff (P := Subgroup.normalizer (V' : Set G)) le_rfl (g ^ 2 ^ j)).mpr
      (by rw [hpow]; exact hC)
  rw [map_pow, hgz] at h1
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have hzo : orderOf zs = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hzs3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hzs1
    · exact h
  rw [hzo] at h2
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem false_of_c27Alt (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit')
    (hC24a : ASC24One G) (hC24b : ASC24TwoChar G) (hF : CharTwo H) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L)
    (h : C27Alt H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  set V' := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hV'
  obtain ⟨⟨n, α, hn5, hn8, -, ⟨hαs, hαk, -⟩, t, htQ, htV, hRt, hord, σ, hσ, hα⟩, -⟩ := h
  have hQN := C.Q_le_normalizer h443 hC24a hC24b hF hK hKq hKM
  have hK2 : CharTwo K := CFSG.Quasithin.A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hF
  obtain ⟨⟨-, h1b, -⟩, -, -⟩ := hC27 H _ _ K _ C.hypC23 hK hKq hK2
    (fun h => hKM (h.trans inf_le_left)) hQN rfl
  have hKV : K ≤ Subgroup.normalizer (V' : Set G) := le_normalizer_omegaOneCenterOf_sup K Q
  have hαker : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → α k = 1 := by
    rintro k ⟨k', hk', hkk'⟩
    have e : k' = k := Subtype.ext hkk'
    subst e
    have : k' ∈ α.ker := by rw [hαk]; assumption
    exact this
  have hαone : ∀ k : ↥K, α k = 1 → (k : G) ∈ pCoreOf 2 K := fun k hk =>
    coe_mem_pCoreOf (by rw [← hαk]; exact hk)
  set ts := conjAct V' ⟨t, htV⟩ with hts
  have hts2 : ts ^ 2 = 1 := hord ▸ pow_orderOf_eq_one ts
  have hQK : Q ⊓ K ≤ pCoreOf 2 K := by
    rintro q ⟨hqQ, hqK⟩
    have hqV : q ∈ Subgroup.normalizer (V' : Set G) := hKV hqK
    have hq' : conjAct V' ⟨q, hqV⟩ ∈ autOn Q V' :=
      Setup.mem_autOn_iff.mpr ⟨⟨q, hqV⟩, hqQ, rfl⟩
    rw [hRt] at hq'
    have hq2 : conjAct V' ⟨q, hqV⟩ = 1 ∨ conjAct V' ⟨q, hqV⟩ = ts := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hq'
      rw [← hi]
      have hts2' : ts ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hts2
      rcases Int.even_or_odd i with ⟨r, hr⟩ | ⟨r, hr⟩
      · left
        rw [hr, ← two_mul, zpow_mul, hts2', one_zpow]
      · right
        rw [hr, zpow_add, zpow_mul, hts2', one_zpow, one_mul, zpow_one]
    rcases hq2 with h1 | h1
    · have hqC : q ∈ Subgroup.centralizer (V' : Set G) :=
        (Setup.rho_eq_one_iff (P := Subgroup.normalizer (V' : Set G)) le_rfl ⟨q, hqV⟩).mp h1
      have hqZ := inf_centralizer_le_oTwoZIn_of_c27 h1b ⟨hqK, hqC⟩
      have hc : α ⟨q, hqK⟩ ∈ Subgroup.center (alternatingGroup (Fin n)) := by
        refine Subgroup.mem_center_iff.mpr fun a => ?_
        obtain ⟨x, rfl⟩ := hαs a
        have h2 := commutator_mem_of_mem_oTwoZIn hqZ x.2
        have h3 : α (x * ⟨q, hqK⟩ * x⁻¹ * (⟨q, hqK⟩ : ↥K)⁻¹) = 1 := hαker _ h2
        rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
        calc α x * α ⟨q, hqK⟩
            = (α x * α ⟨q, hqK⟩ * (α x)⁻¹ * (α ⟨q, hqK⟩)⁻¹) * (α ⟨q, hqK⟩ * α x) := by group
          _ = α ⟨q, hqK⟩ * α x := by rw [h3, one_mul]
      rw [alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega),
        Subgroup.mem_bot] at hc
      exact hαone _ hc
    · exfalso
      set c := q⁻¹ * t with hcdef
      have hcN : c ∈ Subgroup.normalizer (V' : Set G) := Subgroup.mul_mem _ (Subgroup.inv_mem _ hqV) htV
      have hc1 : conjAct V' ⟨c, hcN⟩ = 1 := by
        have e : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (V' : Set G))) =
            (⟨q, hqV⟩ : ↥(Subgroup.normalizer (V' : Set G)))⁻¹ * ⟨t, htV⟩ := rfl
        rw [e, map_mul, map_inv, h1, inv_mul_cancel]
      have hcC : c ∈ Subgroup.centralizer (V' : Set G) :=
        (Setup.rho_eq_one_iff (P := Subgroup.normalizer (V' : Set G)) le_rfl ⟨c, hcN⟩).mp hc1
      have hcKQ : c ∈ K ⊔ Q :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.inv_mem hqK)) (Subgroup.mem_sup_right htQ)
      have hck : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 K := fun k hk =>
        commutator_mem_of_c27 hQN h1b ⟨hcKQ, hcC⟩ hk
      have key : ∀ k : ↥K, σ * (α k : Equiv.Perm (Fin n)) * σ⁻¹ =
          (α ⟨q, hqK⟩ : Equiv.Perm (Fin n)) * α k * (α ⟨q, hqK⟩ : Equiv.Perm (Fin n))⁻¹ := by
        intro k
        have hk' : t * (k : G) * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hQN htQ) k).mp k.2
        have h1' := hα k k.2 hk'
        have hmem : c * (k : G) * c⁻¹ * (k : G)⁻¹ ∈ K := pCoreOf_le 2 K (hck k k.2)
        have e : (⟨t * k * t⁻¹, hk'⟩ : ↥K) =
            ⟨q, hqK⟩ * ((⟨_, hmem⟩ : ↥K) * k) * (⟨q, hqK⟩ : ↥K)⁻¹ := by
          apply Subtype.ext
          show t * (k : G) * t⁻¹ = q * (c * (k : G) * c⁻¹ * (k : G)⁻¹ * k) * q⁻¹
          rw [hcdef]
          group
        have hk1 : α (⟨_, hmem⟩ : ↥K) = 1 := hαker _ (hck k k.2)
        rw [e, map_mul, map_mul, map_inv, map_mul, hk1, one_mul] at h1'
        rw [← h1']
        simp
      have hcomm : ∀ a ∈ alternatingGroup (Fin n),
          ((α ⟨q, hqK⟩ : Equiv.Perm (Fin n))⁻¹ * σ) * a =
            a * ((α ⟨q, hqK⟩ : Equiv.Perm (Fin n))⁻¹ * σ) := by
        intro a ha
        obtain ⟨k, hk⟩ := hαs ⟨a, ha⟩
        have h2 := key k
        rw [hk] at h2
        calc (α ⟨q, hqK⟩ : Equiv.Perm (Fin n))⁻¹ * σ * a
            = (α ⟨q, hqK⟩ : Equiv.Perm (Fin n))⁻¹ * (σ * a * σ⁻¹) * σ := by group
          _ = (α ⟨q, hqK⟩ : Equiv.Perm (Fin n))⁻¹ * ((α ⟨q, hqK⟩ : Equiv.Perm (Fin n)) * a *
              (α ⟨q, hqK⟩ : Equiv.Perm (Fin n))⁻¹) * σ := by rw [h2]
          _ = a * ((α ⟨q, hqK⟩ : Equiv.Perm (Fin n))⁻¹ * σ) := by group
      have h3 := eq_one_of_commute_alternating hn5 hcomm
      have hσq : σ = (α ⟨q, hqK⟩ : Equiv.Perm (Fin n)) := by
        have h4 := congrArg (fun π => (α ⟨q, hqK⟩ : Equiv.Perm (Fin n)) * π) h3
        simpa using h4
      have hsign := hσ.sign_eq
      have hev := (α ⟨q, hqK⟩).2
      rw [Equiv.Perm.mem_alternatingGroup] at hev
      rw [hσq, hev] at hsign
      exact absurd hsign (by decide)
  refine C.not_inf_le_pCoreOf_of_hom hK α hαker (fun X hX => ?_) hQK
  rw [card_map_sylow_eq α hαs hX]
  have hfac : 2 ≤ (Nat.card (alternatingGroup (Fin n))).factorization 2 := by
    interval_cases n <;>
      (rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide +kernel)
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (Nat.card (alternatingGroup (Fin n))).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) hfac

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
