module

public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
public import CFSG.LocalAnalysis.SectionRank.ExceptionalEvenCover

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Alternating

theorem toAdd_allOnes_zpow (n : ℕ) (k : ℤ) (i : Fin n) :
    Multiplicative.toAdd (G6.allOnes n ^ k) i = (k : ZMod 2) := by
  simp [G6.allOnes, toAdd_zpow]

theorem eq_one_of_mem_zpowers_allOnes {n : ℕ} (hn : Odd n) {x : G6.PermMod n}
    (hx : x ∈ Subgroup.zpowers (G6.allOnes n)) (hc : x ∈ G6.coreMod n) : x = 1 := by
  obtain ⟨k, rfl⟩ := hx
  rw [G6.mem_coreMod] at hc
  simp only [toAdd_allOnes_zpow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hc
  rw [ZMod.natCast_eq_one_iff_odd.mpr hn, one_mul] at hc
  apply Multiplicative.toAdd.injective
  funext i
  simp only at hc ⊢
  rw [toAdd_allOnes_zpow, hc]
  rfl

theorem toAdd_eq_of_forall_permAct_eq {n : ℕ} (hn : 3 ≤ n) {x : G6.PermMod n}
    (hx : ∀ σ ∈ alternatingGroup (Fin n), G6.permAct n σ x = x) (i j : Fin n) :
    Multiplicative.toAdd x i = Multiplicative.toAdd x j := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j} := fun k _ => by
      by_cases hk : k = i
      · simp [hk]
      · simp [h k hk]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h2 := Finset.card_le_two (a := i) (b := j)
    omega
  set σ : Equiv.Perm (Fin n) := Equiv.swap j k * Equiv.swap i j with hσ
  have hσA : σ ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, hσ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hkj.symm,
      Equiv.Perm.sign_swap hij]
    rfl
  have h := congrArg (fun y : G6.PermMod n => Multiplicative.toAdd y i) (hx σ hσA)
  simp only [G6.permAct_apply] at h
  have hinv : σ⁻¹ i = j := by
    rw [hσ, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hij hki.symm, Equiv.swap_apply_left]
  rw [hinv] at h
  exact h.symm

theorem eq_one_of_mem_coreMod_of_fixed {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) {x : G6.PermMod n}
    (hx : x ∈ G6.coreMod n) (hfix : ∀ σ ∈ alternatingGroup (Fin n), G6.permAct n σ x = x) :
    x = 1 := by
  have hc := toAdd_eq_of_forall_permAct_eq h3 hfix
  set c := Multiplicative.toAdd x ⟨0, by omega⟩ with hcdef
  have hxc : x = G6.allOnes n ^ (c.val : ℤ) := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_allOnes_zpow, hc i ⟨0, by omega⟩, ← hcdef]
    simp
  exact eq_one_of_mem_zpowers_allOnes hn ⟨_, hxc.symm⟩ hx

theorem fixV_eq_bot_of_alternatingNatural {V : Type*} [CommGroup V] {n : ℕ} (hn : Odd n)
    (h3 : 3 ≤ n) {H : Subgroup (MulAut V)} (h : AlternatingNatural H ⊤ ⊥ n) : fixV H = ⊥ := by
  obtain ⟨π, -, -, -, -, -, -, -, β, -, hβ1, hβeq⟩ := h
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, trivial⟩)
  have hfix : ∀ σ ∈ alternatingGroup (Fin n), G6.permAct n σ m.1 = m.1 := by
    intro σ hσ
    have hmem : (FFModel.altDn n).act ⟨σ, hσ⟩ m.1 ∈ (FFModel.altDn n).sec :=
      G6.permAct_mem_coreMod σ m.2
    have key := hβeq ⟨σ, hσ⟩ ⟨v, trivial⟩ m trivial hmem hm.symm
    have hv' : ((π ⟨σ, hσ⟩ : ↥H) : MulAut V) v = v := hv _ (π ⟨σ, hσ⟩).2
    simp only [hv'] at key
    rw [← hm, QuotientGroup.eq, Subgroup.mem_subgroupOf] at key
    have h1 : m⁻¹ * ⟨_, hmem⟩ = 1 := Subtype.ext (eq_one_of_mem_zpowers_allOnes hn key.1 key.2)
    rw [inv_mul_eq_one] at h1
    exact (congrArg Subtype.val h1).symm
  have hm1 : m = 1 := Subtype.ext (eq_one_of_mem_coreMod_of_fixed hn h3 m.2 hfix)
  have : β ⟨v, trivial⟩ = 1 := by
    rw [← hm, hm1]
    rfl
  exact (hβ1 _).mp this

end Alternating

theorem not_isPerfect_perm_fin_six : ¬ Group.IsPerfect (Equiv.Perm (Fin 6)) := by
  intro h
  have hle : commutator (Equiv.Perm (Fin 6)) ≤ Equiv.Perm.sign.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [h.commutator_eq_top] at hle
  have hs := hle (Subgroup.mem_top (Equiv.swap (0 : Fin 6) 1))
  rw [MonoidHom.mem_ker, Equiv.Perm.sign_swap (by decide)] at hs
  exact absurd hs (by decide)

theorem not_isPerfect_statedSp_of_card_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : ¬ Group.IsPerfect ↥(StatedSp 2 K) := by
  intro _
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  exact not_isPerfect_perm_fin_six (Group.IsPerfect.ofSurjective
    (f := (QuasithinUnique.Bridge.Alt57Model.spEquivPerm K hK').toMonoidHom)
    (QuasithinUnique.Bridge.Alt57Model.spEquivPerm K hK').surjective)

theorem lieModel_psp_of_mulEquiv_statedSp {Q : Type} [Group Q] {K : Type} [Field K] [Finite K]
    {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) (e : Q ≃* ↥(StatedSp 2 K)) :
    LieModel Q .PSp 2 2 m := by
  have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
  have h4 : 4 ≤ 2 ^ m := (Nat.pow_le_pow_right two_pos hm).trans_eq' (by norm_num)
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, le_rfl, ?_⟩, K, inferInstance,
    inferInstance, hK, ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSp_eq_bot 2)).trans
      QuotientGroup.quotientBot).symm⟩⟩
  intro h
  have := congrArg Prod.snd h
  simp only at this
  omega

theorem nonempty_mulEquiv_of_surjective_of_isSimpleGroup {Γ H : Type*} [Group Γ] [Group H]
    [IsSimpleGroup Γ] (hH : ∃ h : H, h ≠ 1) (π : Γ →* H) (hπ : Function.Surjective π) :
    Nonempty (H ≃* Γ) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact ⟨(MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp h, hπ⟩).symm⟩
  · exfalso
    obtain ⟨y, hy⟩ := hH
    obtain ⟨x, rfl⟩ := hπ y
    exact hy ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x))

variable {G : Type} [Group G]

theorem autOn_eq_autOn_sup_of_isSimpleGroup {L T V : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (V : Set G)) (hT : T ≤ Subgroup.normalizer (V : Set G))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hs : IsSimpleGroup ↥(autOn (L ⊔ T) V))
    (hne : autOn L V ≠ ⊥) : autOn L V = autOn (L ⊔ T) V := by
  have hle : autOn L V ≤ autOn (L ⊔ T) V := A4.autOn_mono le_sup_left
  have hN : autOn (L ⊔ T) V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) := by
    rw [autOn_sup_eq_sup_autOn hL hT]
    exact sup_le Subgroup.le_normalizer (autOn_le_normalizer_autOn hL hT hTL)
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((autOn L V).subgroupOf (autOn (L ⊔ T) V))
    with h | h
  · exfalso
    apply hne
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_self.mp (h.mono_right hle)
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

theorem autOn_ne_bot_of_not_le_centralizer {L V : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (V : Set G)) (hnc : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    autOn L V ≠ ⊥ :=
  CFSG.Quasithin.AutOn.autOn_ne_bot_of_not_le_centralizer hL hnc

theorem exists_ne_one_autOn {L V : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hnc : ¬ L ≤ Subgroup.centralizer (V : Set G)) : ∃ a : ↥(autOn L V), a ≠ 1 := by
  by_contra h
  push Not at h
  apply autOn_ne_bot_of_not_le_centralizer hL hnc
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val (h ⟨a, ha⟩)

end CFSG.Quasithin.H13
