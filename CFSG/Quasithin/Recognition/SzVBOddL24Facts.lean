module

public import CFSG.Quasithin.Recognition.SzVBBridge
public import CFSG.Quasithin.Recognition.SzVBKer

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Holt.H78

structure L24Facts {G : Type*} [Group G] (P S V : Subgroup G) : Prop where
  card_five : Nat.card (ConjSet P V) = 5
  S_le : S ≤ P
  S_pGroup : IsPGroup 2 S
  S_le_normalizer : S ≤ Subgroup.normalizer (V : Set G)
  ker_inv_le : ∀ x : ↥P, x * x = 1 → x ∈ kerAct P V → (x : G) ∈ pCoreOf 2 P
  S_transitive : ∀ U U' : ConjSet P V, U ≠ ConjSet.base P V → U' ≠ ConjSet.base P V →
    ∃ s : ↥P, (s : G) ∈ S ∧ s • U = U'


variable {G : Type} [Group G] [Finite G]

theorem exists_mem_smul_eq_of_bender {K P S V : Subgroup G} {n i e : ℕ} (hKP : K ≤ P)
    (hSyl : IsSylowTwoOf (S ⊓ K) K) (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hA : IsBenderAction ↥(imgK K P V) (ConjSet P V) n i e) {U U' : ConjSet P V}
    (hU : U ≠ ConjSet.base P V) (hU' : U' ≠ ConjSet.base P V) :
    ∃ s : ↥P, (s : G) ∈ S ∧ s • U = U' := by
  obtain ⟨g, hgs, hg⟩ := exists_surjective_imgK V hKP
  have hp : IsPGroup 2 ((S ⊓ K).subgroupOf K) := hSyl.2.1.comap_subtype
  obtain ⟨Q, hQeq⟩ : ∃ Q : Sylow 2 ↥(imgK K P V),
      (Q : Subgroup ↥(imgK K P V)) = ((S ⊓ K).subgroupOf K).map g :=
    ⟨(hp.map g).toSylow fun h =>
      hSyl.2.2 (h.trans (((S ⊓ K).subgroupOf K).index_map_dvd hgs)), rfl⟩
  have hQ : (Q : Subgroup ↥(imgK K P V)) ≤
      MulAction.stabilizer ↥(imgK K P V) (ConjSet.base P V) := by
    intro q hq
    rw [hQeq] at hq
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hq
    rw [MulAction.mem_stabilizer_iff]
    show ((g t : ↥(imgK K P V)) : Equiv.Perm (ConjSet P V)) (ConjSet.base P V) =
      ConjSet.base P V
    rw [hg]
    exact Subtype.ext (OddAux.conjSub_eq_of_mem_normalizer'
      (hSV (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1))
  obtain ⟨p, hpQ, hpU⟩ := hA.exists_mem_smul_eq hQ hU hU'
  rw [hQeq] at hpQ
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hpQ
  exact ⟨Subgroup.inclusion hKP t,
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1, (hg t U).symm.trans hpU⟩

theorem exists_order_three_of_bender {K P V B : Subgroup G} (hKP : K ≤ P)
    (hA : IsBenderAction ↥(imgK K P V) (ConjSet P V) 2 1 1)
    (hB : K ⊓ Subgroup.normalizer (V : Set G) ≤ B) :
    ∃ t : ↥P, (t : G) ∈ B ∧ Odd (orderOf (t : G)) ∧
      MulAction.toPermHom ↥P (ConjSet P V) t ≠ 1 ∧
      (MulAction.toPermHom ↥P (ConjSet P V) t) ^ 3 = 1 := by
  have : Nontrivial (ConjSet P V) := hA.nontrivial
  obtain ⟨β, hβ⟩ := exists_ne (ConjSet.base P V)
  have hcard : Nat.card ↥(MulAction.stabilizer ↥(imgK K P V) (ConjSet.base P V) ⊓
      MulAction.stabilizer ↥(imgK K P V) β) = 3 :=
    (hA.card_stabilizer_inf hβ.symm).trans (by norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 3 (dvd_of_eq hcard.symm)
  obtain ⟨g, hgs, hg⟩ := exists_surjective_imgK V hKP
  obtain ⟨k, hk⟩ := hgs σ.1
  have hfix : Subgroup.inclusion hKP k • ConjSet.base P V = ConjSet.base P V := by
    have h1 := hg k (ConjSet.base P V)
    rw [hk] at h1
    exact h1.symm.trans (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp σ.2).1)
  have hkN : (k : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq]
    exact congrArg Subtype.val hfix
  obtain ⟨t₁, ht₁B, himg⟩ : ∃ t₁ : ↥P, (t₁ : G) ∈ B ∧
      MulAction.toPermHom ↥P (ConjSet P V) t₁ =
        ((σ.1 : ↥(imgK K P V)) : Equiv.Perm (ConjSet P V)) := by
    refine ⟨Subgroup.inclusion hKP k, hB ⟨k.2, hkN⟩, ?_⟩
    ext U
    exact (hg k U).symm.trans
      (congrArg (fun x : ↥(imgK K P V) => (x : Equiv.Perm (ConjSet P V)) U) hk)
  have hτ : orderOf ((σ.1 : ↥(imgK K P V)) : Equiv.Perm (ConjSet P V)) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hσ]
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t₁).ne'
  have hordt : orderOf (t₁ ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hord⟩, hord]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hcop : Nat.Coprime (orderOf ((σ.1 : ↥(imgK K P V)) : Equiv.Perm (ConjSet P V)))
      (2 ^ a) := by
    rw [hτ]
    exact Nat.Coprime.pow_right a (by decide)
  have hτpow : orderOf (MulAction.toPermHom ↥P (ConjSet P V) (t₁ ^ 2 ^ a)) = 3 := by
    rw [map_pow, himg, hcop.orderOf_pow, hτ]
  refine ⟨t₁ ^ 2 ^ a, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact B.pow_mem ht₁B _
  · rw [Subgroup.orderOf_coe, hordt]
    exact hm
  · intro h1
    rw [h1, orderOf_one] at hτpow
    omega
  · have h1 := pow_orderOf_eq_one (MulAction.toPermHom ↥P (ConjSet P V) (t₁ ^ 2 ^ a))
    rwa [hτpow] at h1

variable {K1 L2 S Zs : Subgroup G}

theorem isBenderAction_imgK_L24 (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hL : IsL2Quot 2 (OTwoQuot K1)) :
    IsBenderAction ↥(imgK K1 (K1 ⊔ S) (conjClosure Zs L2))
      (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) 2 1 1 := by
  obtain ⟨e⟩ := hL
  have hSyl : IsSylowTwoOf (S ⊓ K1) K1 := h.hyp.h1.sylow
  have hP : IsPGroup 2 ((S ⊓ K1).subgroupOf K1) := hSyl.2.1.comap_subtype
  obtain ⟨Qs, hQs⟩ : ∃ Qs : Sylow 2 ↥K1, (Qs : Subgroup ↥K1) = (S ⊓ K1).subgroupOf K1 :=
    ⟨hP.toSylow hSyl.2.2, rfl⟩
  have hker : (MonoidHom.id (OTwoQuot K1)).ker ≤ Subgroup.center (OTwoQuot K1) := by simp
  have hπ : Function.Surjective ((MonoidHom.id (OTwoQuot K1)).comp
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1))) :=
    Function.surjective_id.comp (QuotientGroup.mk'_surjective _)
  exact exists_isBenderAction_imgK_of_bender (B := borelOf K1 S) le_sup_left
    (fun k hk k' hk' => conjSub_eq_iff_mem_borelOf hRO h hk hk')
    (fun x hx => exists_mem_K1_conjSub h hRO hx)
    ((MonoidHom.id (OTwoQuot K1)).comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1))) hπ Qs
    (fun k => by
      rw [hQs]
      exact (CFSG.Quasithin.Background.Harris.R1.mem_borelOf_iff_mem_normalizer k).symm)
    (ker_le_normalizer_of_central hSyl (MonoidHom.id _) hker Qs hQs)
    (CFSG.GH74.Uniqueness.Bender.BenderType.linear 2 le_rfl e)

theorem l24Facts_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hL : IsL2Quot 2 (OTwoQuot K1)) : L24Facts (K1 ⊔ S) S (conjClosure Zs L2) := by
  have hA := isBenderAction_imgK_L24 hRO h hL
  have hSV := S_le_normalizer_conjClosure hRO h
  exact ⟨hA.card_eq.trans (by norm_num), le_sup_right, h.hyp.h1.pgroup, hSV,
    ker_inv_le_of_setting hRO h (n := 2) le_rfl (Or.inl hL),
    fun _ _ hU hU' => exists_mem_smul_eq_of_bender le_sup_left h.hyp.h1.sylow hSV hA hU hU'⟩

theorem exists_order_three (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hL : IsL2Quot 2 (OTwoQuot K1)) :
    ∃ t : ↥(K1 ⊔ S), (t : G) ∈ borelOf K1 S ∧ Odd (orderOf (t : G)) ∧
      MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) t ≠ 1 ∧
      (MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) t) ^ 3 = 1 :=
  exists_order_three_of_bender le_sup_left (isBenderAction_imgK_L24 hRO h hL)
    (inf_normalizer_eq_borelOf hRO h).le

end CFSG.Quasithin.SzVB
