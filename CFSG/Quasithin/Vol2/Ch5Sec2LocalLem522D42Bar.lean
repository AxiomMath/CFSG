module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42IdentExc
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.H13.D42

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem card_of_lieModel_PSL2 {X : Type} [Group X] {k : ℕ} (h : LieModel X .PSL 2 2 k) :
    Nat.card X = 2 ^ k * (4 ^ k - 1) ∧ 2 ≤ k := by
  have hs := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  obtain ⟨⟨-, hk1, -, hne, -⟩, -⟩ := id hs
  have hk : 2 ≤ k := by
    by_contra hlt
    exact hne (by rw [show k = 1 by omega]; rfl)
  refine ⟨?_, hk⟩
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hs).1 rfl, ordA]
  have h4 : (4 : ℕ) ^ k = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hodd : Nat.gcd (1 + 1) (2 ^ k - 1) = 1 :=
    Nat.coprime_two_left.mpr (Nat.Even.sub_odd (Nat.one_le_two_pow) (by
      rw [Nat.even_pow]; exact ⟨even_two, by omega⟩) odd_one)
  rw [h4, hodd, Nat.div_one]
  simp

theorem k_eq_three {k : ℕ} (hk : 2 ≤ k) (h : 2 ^ k * (4 ^ k - 1) ∣ 211341312) : k = 3 := by
  have hle := Nat.le_of_dvd (by norm_num) h
  have hk14 : k < 14 := by
    by_contra hge
    have h1 : 2 ^ 14 * (4 ^ 14 - 1) ≤ 2 ^ k * (4 ^ k - 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1)
    omega
  interval_cases k <;> first | rfl | norm_num at h

variable {G : Type} [Group G] [Finite G]

theorem bar_facts {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh)
    (hsimple : IsSimpleGroup (O2Q K)) :
    Group.IsPerfect ↥(modO2Image X Kh) ∧
      IsSylowTwoOf ((o2Img X S ⊓ modO2Image X Kh).subgroupOf (modO2Image X Kh)) ⊤ ∧
      modO2Image X K ≤ modO2Image X Kh ∧
      ⁅(modO2Image X K).subgroupOf (modO2Image X Kh),
        (modO2Image X K).subgroupOf (modO2Image X Kh)⁆ =
          (modO2Image X K).subgroupOf (modO2Image X Kh) ∧
      (modO2Image X K).subgroupOf (modO2Image X Kh) ≠ ⊥ ∧
      (o2Img X S ⊓ modO2Image X Kh).subgroupOf (modO2Image X Kh) ≤
        Subgroup.normalizer (((modO2Image X K).subgroupOf (modO2Image X Kh) :
          Subgroup ↥(modO2Image X Kh)) : Set ↥(modO2Image X Kh)) ∧
      (modO2Image X K).subgroupOf (modO2Image X Kh) ⊔
        (o2Img X S ⊓ modO2Image X Kh).subgroupOf (modO2Image X Kh) ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := modO2Image X Kh with hY
  set Ub := o2Img X S ⊓ Y with hUb
  have hUbY : IsSylowTwoOf Ub Y :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp l.hatBar_cComp) l.sylowBar
  set U := Ub.subgroupOf Y with hU
  have hUS : IsSylowTwoOf U ⊤ := isSylowTwoOf_top_subgroupOf hUbY
  set Kb := modO2Image X K with hKb
  have hKbY : Kb ≤ Y := Subgroup.map_mono fun x hx => l.le_hat hx
  set KS := Kb.subgroupOf Y with hKS
  have hKbperf : ⁅Kb, Kb⁆ = Kb := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr l.perfect
    have : Group.IsPerfect ↥Kb := Group.IsPerfect.ofSurjective (barMap_surjective l.le_X)
    exact Subgroup.isPerfect_iff.mp this
  have hKSperf : ⁅KS, KS⁆ = KS := by
    have : Group.IsPerfect ↥Kb := Subgroup.isPerfect_iff.mpr hKbperf
    have : Group.IsPerfect ↥KS :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKbY).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Subgroup.isPerfect_iff.mp this
  have hKbne : Kb ≠ ⊥ := by
    intro hbot
    obtain ⟨eB⟩ := l.bar_equiv
    have : Subsingleton (ModO2 (modO2Image X K)) := by
      have : Subsingleton ↥(modO2Image X K) := by
        rw [← hKb, hbot]
        infer_instance
      infer_instance
    have : Nontrivial (O2Q K) := hsimple.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (O2Q K)
    exact hab (eB.injective (Subsingleton.elim _ _))
  have hKSne : KS ≠ ⊥ := by
    intro hbot
    apply hKbne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hKbY hx⟩ : ↥Y) ∈ KS := hx
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hTKb : o2Img X S ≤ Subgroup.normalizer ((Kb : Subgroup (O2Q X)) : Set (O2Q X)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact o2Map_mem_normalizer (l.normalizes (Subgroup.mem_subgroupOf.mp ht))
  have hUKS : U ≤ Subgroup.normalizer ((KS : Subgroup ↥Y) : Set ↥Y) :=
    le_normalizer_subgroupOf (inf_le_left.trans hTKb)
  have hSperf : Group.IsPerfect ↥Y := by
    have : Group.IsPerfect ↥Kh := Subgroup.isPerfect_iff.mpr l.hat_cComp.2.1
    have : Group.IsPerfect (O2Q Kh) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Kh))
    obtain ⟨eH⟩ := l.hat_equiv
    exact Group.IsPerfect.ofSurjective (f := eH.toMonoidHom) eH.surjective
  have hne : KS ⊔ U ≠ ⊤ := by
    intro htop
    have h1 : (⊤ : Subgroup ↥Y) ≤ KS :=
      le_of_perfect_of_le_sup (Subgroup.isPerfect_iff.mp inferInstance) htop.ge hUS.2.1 hUKS
    have h2 : Y ≤ Kb := by
      intro y hy
      exact h1 (Subgroup.mem_top (⟨y, hy⟩ : ↥Y))
    exact lt_irrefl _ (lt_of_lt_of_le l.bar_lt h2)
  exact ⟨hSperf, hUS, hKbY, hKSperf, hKSne, hUKS, hne⟩

theorem is3D4_bar
    {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh) {k : ℕ}
    (htype : (SuzukiModel (O2Q K) 2 k ∧ Is2F4 k (O2Q Kh)) ∨
      (LieModel (O2Q K) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q Kh)))
    (hres : ∃ U P : Subgroup (O2Q Kh), IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ P ⋖ ⊤ ∧
      Group.IsSolvable ↥P) :
    LieModel (O2Q K) .PSL 2 2 3 ∧ Is3D4 2 1 ↥(modO2Image X Kh) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup (O2Q K) := by
    rcases htype with ⟨hS, -⟩ | ⟨hL2, -⟩
    · exact isSimpleGroup_of_psl2_or_sz (Or.inr hS)
    · exact isSimpleGroup_of_lieModel_PSL2 hL2
  obtain ⟨hSperf, hUS, hKbY, hKSperf, hKSne, hUKS, hne⟩ := bar_facts l hsimple
  obtain ⟨eH⟩ := l.hat_equiv
  have hYnt : Nontrivial ↥(modO2Image X Kh) := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKSne
    exact ⟨⟨(a : ↥(modO2Image X Kh)), 1, fun h => ha (Subtype.ext h)⟩⟩
  have hKSns : ¬ Group.IsSolvable ↥((modO2Image X K).subgroupOf (modO2Image X Kh)) := by
    have : Group.IsPerfect ↥((modO2Image X K).subgroupOf (modO2Image X Kh)) :=
      Subgroup.isPerfect_iff.mpr hKSperf
    have : Nontrivial ↥((modO2Image X K).subgroupOf (modO2Image X Kh)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hKSne
    exact Group.IsPerfect.not_isSolvable _
  rcases htype with ⟨-, h2F4⟩ | ⟨hL2, hR2⟩
  · exfalso
    have : Group.IsPerfect ↥Kh := Subgroup.isPerfect_iff.mpr l.hat_cComp.2.1
    have : Group.IsPerfect (O2Q Kh) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Kh))
    have : Nontrivial (O2Q Kh) := eH.symm.injective.nontrivial
    obtain ⟨P₀⟩ : Nonempty (Sylow 2 (O2Q Kh)) := inferInstance
    exact false_of_is2F4 h2F4 (isSylowTwoOf_top_of_sylow P₀) hres
  · obtain ⟨hcard, hk⟩ := card_of_lieModel_PSL2 hL2
    obtain ⟨eB⟩ := l.bar_equiv
    have hdvd : 2 ^ k * (4 ^ k - 1) ∣
        Nat.card ↥((modO2Image X K).subgroupOf (modO2Image X Kh)) := by
      rw [← hcard, Nat.card_congr eB.toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKbY).toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    have hD4 := is3D4_of_solvable_max (IsRank2LieChar2.of_mulEquiv eH hR2) hUS hKSns hne hk hdvd
      (exists_solvable_max_of_mulEquiv eH hres)
    have hY : Nat.card ↥(modO2Image X Kh) = 211341312 := by
      rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD4]
      show ordTrialityD4 (2 ^ 1) = 211341312
      decide
    obtain rfl : k = 3 :=
      k_eq_three hk (hY ▸ hdvd.trans (Subgroup.card_subgroup_dvd_card _))
    exact ⟨hL2, hD4⟩

end CFSG.Quasithin.H13.D42
