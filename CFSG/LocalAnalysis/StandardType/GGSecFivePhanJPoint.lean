module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCoord
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpStdSubCoord
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpStdSub
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupMemberRoots
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggDReflect_single_sub_single {k : ℕ} {ε : Fin k → ℤ} (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    {a b c : Fin k} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ggDReflect (Pi.single a (ε a) - Pi.single b (ε b)) (Pi.single b (ε b) - Pi.single c (ε c)) =
      Pi.single a (ε a) - Pi.single c (ε c) := by
  have hγ : (Pi.single a (ε a) - Pi.single b (ε b) : Fin k → ℤ) =
      Pi.single a (ε a) + Pi.single b (-(ε b)) := by
    rw [sub_eq_add_neg, Pi.single_neg]
  have hδ : (Pi.single b (ε b) - Pi.single c (ε c) : Fin k → ℤ) =
      Pi.single b (ε b) + Pi.single c (-(ε c)) := by
    rw [sub_eq_add_neg, Pi.single_neg]
  have hdot : ggDDot (Pi.single b (ε b) - Pi.single c (ε c))
      (Pi.single a (ε a) - Pi.single b (ε b)) = -1 := by
    rw [hδ, hγ, ggDDot_single_add_single,
      ggDPair_apply_right hab (ε a) (-(ε b)),
      ggDPair_apply_of_ne (fun h => hac h.symm) (fun h => hbc h.symm) (ε a) (-(ε b))]
    rcases hε b with h | h <;> simp [h]
  rw [ggDReflect, hdot, neg_one_smul]
  abel

theorem ggD_single_sub_single_mem_of_chain {k : ℕ} {Φ : Set (Fin k → ℤ)} {ε : Fin k → ℤ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hneg : ∀ η ∈ Φ, -η ∈ Φ)
    (hrefl : ∀ γ ∈ Φ, ∀ δ ∈ Φ, ggDReflect γ δ ∈ Φ) {a b c : Fin k} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (h₁ : Pi.single a (ε a) - Pi.single b (ε b) ∈ Φ)
    (h₂ : Pi.single b (ε b) - Pi.single c (ε c) ∈ Φ) :
    ∀ x ∈ ({a, b, c} : Finset (Fin k)), ∀ y ∈ ({a, b, c} : Finset (Fin k)), x ≠ y →
      Pi.single x (ε x) - Pi.single y (ε y) ∈ Φ := by
  have h_ac : Pi.single a (ε a) - Pi.single c (ε c) ∈ Φ := by
    have h3 := hrefl _ h₁ _ h₂
    rwa [ggDReflect_single_sub_single hε hab hbc hac] at h3
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact h₁
  · exact h_ac
  · simpa only [neg_sub] using hneg _ h₁
  · exact absurd rfl hxy
  · exact h₂
  · simpa only [neg_sub] using hneg _ h_ac
  · simpa only [neg_sub] using hneg _ h₂
  · exact absurd rfl hxy

theorem ggD_exists_chain_of_meet {k : ℕ} {Φ : Set (Fin k → ℤ)} {ε : Fin k → ℤ}
    (hneg : ∀ η ∈ Φ, -η ∈ Φ) {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d)
    (h₁ : Pi.single a (ε a) - Pi.single b (ε b) ∈ Φ)
    (h₂ : Pi.single c (ε c) - Pi.single d (ε d) ∈ Φ)
    (hmeet : ∃ y : Fin k, y ∈ ({a, b} : Finset (Fin k)) ∧ y ∈ ({c, d} : Finset (Fin k)))
    (hne : ({a, b} : Finset (Fin k)) ≠ {c, d}) :
    ∃ x y z : Fin k, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Pi.single x (ε x) - Pi.single y (ε y) ∈ Φ ∧
      Pi.single y (ε y) - Pi.single z (ε z) ∈ Φ := by
  obtain ⟨y, hy1, hy2⟩ := hmeet
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy1 hy2
  rcases hy1 with hya | hyb
  · rcases hy2 with hyc | hyd
    ·
      have hca : c = a := hyc.symm.trans hya
      refine ⟨b, a, d, hab.symm, by simpa [hca] using hcd, ?_,
        by simpa only [neg_sub] using hneg _ h₁, by simpa [hca] using h₂⟩
      intro hbd
      exact hne (by simp [hca, hbd])
    ·
      have hda : d = a := hyd.symm.trans hya
      refine ⟨c, a, b, by simpa [hda] using hcd, hab, ?_,
        by simpa [hda] using h₂, h₁⟩
      intro hcb
      exact hne (by rw [hcb, hda, Finset.pair_comm])
  · rcases hy2 with hyc | hyd
    ·
      have hcb : c = b := hyc.symm.trans hyb
      refine ⟨a, b, d, hab, by simpa [hcb] using hcd, ?_, h₁, by simpa [hcb] using h₂⟩
      intro had
      exact hne (by rw [hcb, had, Finset.pair_comm])
    ·
      have hdb : d = b := hyd.symm.trans hyb
      have hbc : b ≠ c := fun h => hcd (h.symm.trans hdb.symm)
      refine ⟨a, b, c, hab, hbc, ?_, h₁, ?_⟩
      · intro hac
        exact hne (by simp [hac, hdb])
      · have h₂' : Pi.single c (ε c) - Pi.single b (ε b) ∈ Φ := by simpa [hdb] using h₂
        have := hneg _ h₂'
        simpa only [neg_sub] using this

theorem ggDk_stdSub_point_phan {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι} (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    {ε : Fin k → ℤ} (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (hΦL : ggDMemberRoots e φ L =
      {η | ∃ a b : Fin k, a ≠ b ∧ η = Pi.single a (ε a) - Pi.single b (ε b)})
    (hfix : ∃ xb : ↥Bs, (xb : G) = x ∧ ∀ (u : M.Group) (η : Fin k → ℤ), GGDReflRoot k (φ u) η →
      ((((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb = xb) ↔ ggDDot ε η = 0))
    (hcard : Nat.card Bs = p ^ k) {r r' : MulAut ↥Bs} (hr : r ∈ ggAutomizer J Bs)
    (hr' : r' ∈ ggAutomizer J Bs) (hrr : GGIsReflection p r) (hrr' : GGIsReflection p r')
    (h3 : orderOf (r * r') = 3) :
    ∃ (I : Finset (Fin k)) (v : ↥Bs) (θ : Additive ↥Bs ≃+ (Fin k → ZMod p)), I.card = 3 ∧
      D = Subgroup.closure {x, (v : G)} ∧ p ∣ Nat.card J ∧
      (∀ a ∈ I, ∀ b ∈ I, a ≠ b →
        Pi.single a (ε a) - Pi.single b (ε b) ∈ ggDMemberRoots e φ J) ∧
      (∀ a ∈ I, θ (Additive.ofMul v) a = 0) ∧
      ∀ (u : M.Group) (η : Fin k → ℤ), GGDReflRoot k (φ u) η → ∀ b : ↥Bs,
        θ (Additive.ofMul (((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b)) =
          θ (Additive.ofMul b) - (∑ a, θ (Additive.ofMul b) a * (η a : ZMod p)) •
            fun a => (η a : ZMod p) := by
  classical
  have hp : p.Prime := hcfg.1.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hpFact : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hcfg.1.1.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨hDB, -, hDcard, hxD, -, hJ, hDJ⟩ := hcfg.1.1.2.2.1
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  obtain ⟨xb, rfl, hfx⟩ := hfix
  let ρ : ggWeylD k →* MulAut ↥Bs :=
    (ggAutomizerJoin L Bs 𝒦).subtype.comp (e.toMonoidHom.comp φ.symm.toMonoidHom)
  have hρu : ∀ u, ρ (φ u) = ((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := fun u => by
    simp [ρ]
  have hρ : Function.Injective ρ := fun w w' h =>
    φ.symm.injective (e.injective (Subtype.val_injective (by simpa [ρ] using h)))
  obtain ⟨θ, hθ⟩ := ggDk_exists_coord hp hp2 hBs hk hcard hρ fun a => by
    rw [← hφ a, hρu]
    exact hpres.2 (σ a)
  have hfixθ : ∀ (u : M.Group) (η : Fin k → ℤ), GGDReflRoot k (φ u) η → ∀ b : ↥Bs,
      ((((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b) ↔
        ∑ a, θ (Additive.ofMul b) a * (η a : ZMod p) = 0) := by
    intro u η hu b
    rw [← hρu u]
    constructor
    · intro h
      have h1 := hθ (φ u) η hu b
      rw [h, eq_comm, sub_eq_self] at h1
      obtain ⟨c, -, -, hc, -⟩ := ggDRootSet_exists_pair (hu.mem (by omega))
      have hc1 : (η c : ZMod p) ≠ 0 := by
        rcases ggDRootSet_sign (hu.mem (by omega)) hc with h | h <;> simp [h]
      have h2 := congrFun h1 c
      rw [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at h2
      exact h2.resolve_right hc1
    · intro h
      apply Additive.ofMul.injective
      apply θ.injective
      rw [hθ (φ u) η hu b, h, zero_smul]
      exact sub_zero _
  have hA : ggAutomizer J Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    le_trans (ggAutomizer_mono Bs hJL) (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
  have hrc : r ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hA hr) hrr
  have hrc' : r' ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hA hr') hrr'
  obtain ⟨w, i, hri⟩ := hrc
  obtain ⟨w', i', hri'⟩ := hrc'
  let u : M.Group := w * M.simple i * w⁻¹
  let u' : M.Group := w' * M.simple i' * w'⁻¹
  have heu : ((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = r := by simpa [u] using hri.symm
  have heu' : ((e u' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = r' := by simpa [u'] using hri'.symm
  obtain ⟨γ, hγ⟩ := exists_ggDReflRoot_of_conj φ hφ w i
  obtain ⟨γ', hγ'⟩ := exists_ggDReflRoot_of_conj φ hφ w' i'
  have hγJ : γ ∈ ggDMemberRoots e φ J := ⟨u, hγ, by rw [heu]; exact hr⟩
  have hγJ' : γ' ∈ ggDMemberRoots e φ J := ⟨u', hγ', by rw [heu']; exact hr'⟩
  have hγL : γ ∈ ggDMemberRoots e φ L := ⟨u, hγ, by rw [heu]; exact ggAutomizer_mono Bs hJL hr⟩
  have hγL' : γ' ∈ ggDMemberRoots e φ L := ⟨u', hγ', by rw [heu']; exact ggAutomizer_mono Bs hJL hr'⟩
  rw [hΦL] at hγL hγL'
  obtain ⟨a, b, hab, hγeq⟩ := hγL
  obtain ⟨c, d, hcd, hγ'eq⟩ := hγL'
  have h3uv : orderOf (φ u * φ u') = 3 := by
    have h1 : orderOf (r * r') = orderOf (u * u') := by
      have huu : r * r' = ((e (u * u') : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
        rw [map_mul, Subgroup.coe_mul, heu, heu']
      rw [huu, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    have h2 : orderOf (φ u * φ u') = orderOf (u * u') := by
      rw [← map_mul, MulEquiv.orderOf_eq]
    rw [h1] at h3
    rw [h2]
    exact h3
  have hdisj_comm : ∀ (γ γ' : Fin k → ℤ), (∀ x : Fin k, γ x = 0 ∨ γ' x = 0) →
      ggDDot γ γ' = 0 := by
    intro γ γ' hdisj
    rw [ggDDot, Finset.sum_eq_zero]
    intro x _
    rcases hdisj x with h | h <;> simp [h]
  have hsq_u : φ u * φ u = 1 := by
    have h1 : ((e (u * u) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = 1 := by
      rw [map_mul, Subgroup.coe_mul, heu]
      exact hrr.1
    have h2 : (e (u * u) : ↥(ggAutomizerJoin L Bs 𝒦)) = 1 := Subtype.val_injective h1
    have h3 : u * u = 1 := e.injective (by simpa using h2)
    rw [← map_one φ, ← map_mul, h3, map_one]
  have hsq_u' : φ u' * φ u' = 1 := by
    have h1 : ((e (u' * u') : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = 1 := by
      rw [map_mul, Subgroup.coe_mul, heu']
      exact hrr'.1
    have h2 : (e (u' * u') : ↥(ggAutomizerJoin L Bs 𝒦)) = 1 := Subtype.val_injective h1
    have h3 : u' * u' = 1 := e.injective (by simpa using h2)
    rw [← map_one φ, ← map_mul, h3, map_one]
  have hinter : ¬ (∀ x : Fin k, γ x = 0 ∨ γ' x = 0) := by
    intro hdisj
    have h0 : ggDDot γ γ' = 0 := hdisj_comm γ γ' hdisj
    have hcomm : φ u * φ u' = φ u' * φ u :=
      GGDReflRoot.commute_of_dot_eq_zero (by omega) hγ hγ' h0
    have h2 : (φ u * φ u') ^ 2 = 1 := by
      rw [Commute.mul_pow hcomm, pow_two, hsq_u, pow_two, hsq_u', mul_one]
    have hdvd : orderOf (φ u * φ u') ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have h2dvd : (3 : ℕ) ∣ 2 := by
      rw [← h3uv]
      exact hdvd
    norm_num at h2dvd
  have hne_supp : ¬ ({a, b} : Finset (Fin k)) = {c, d} := by
    intro hsupp
    have hγ'disj : γ' = γ ∨ γ' = -γ := by
      have hc : c = a ∨ c = b := by
        have : c ∈ ({a, b} : Finset (Fin k)) := by rw [hsupp]; simp
        simpa using this
      have hd : d = a ∨ d = b := by
        have : d ∈ ({a, b} : Finset (Fin k)) := by rw [hsupp]; simp
        simpa using this
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · exact absurd rfl hcd
      · left; rw [hγeq, hγ'eq]
      · right; rw [hγeq, hγ'eq]; ring
      · exact absurd rfl hcd
    have hγu : GGDReflRoot k (φ u) γ := by simpa [u] using hγ
    have hγ'u : GGDReflRoot k (φ u') γ' := by simpa [u'] using hγ'
    have heq : φ u = φ u' := GGDReflRoot.unique (by omega) hγu hγ'u hγ'disj
    have h1 : φ u * φ u' = 1 := by rw [heq, hsq_u']
    rw [h1] at h3uv
    norm_num at h3uv
  have hshare : ∃ x : Fin k, x ∈ ({a, b} : Finset (Fin k)) ∧ x ∈ ({c, d} : Finset (Fin k)) := by
    by_contra h
    push Not at h
    have hdisj : ∀ x : Fin k, γ x = 0 ∨ γ' x = 0 := by
      intro x
      by_cases hxa : x = a
      · rw [hxa]
        have hnotin : a ∉ ({c, d} : Finset (Fin k)) := by
          simpa using h a (by simp)
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotin
        right
        rw [hγ'eq]
        simp [hnotin.1, hnotin.2]
      · by_cases hxb : x = b
        · rw [hxb]
          have hnotin : b ∉ ({c, d} : Finset (Fin k)) := by
            simpa using h b (by simp)
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotin
          right
          rw [hγ'eq]
          simp [hnotin.1, hnotin.2]
        · left
          rw [hγeq]
          simp [hxa, hxb]
    exact hinter hdisj
  have hΦJ : GGDSubsys k (ggDMemberRoots e φ J) := ggDMemberRoots_subsys (by omega) φ J
  have hnegJ : ∀ η ∈ ggDMemberRoots e φ J, -η ∈ ggDMemberRoots e φ J :=
    fun _ hη => hΦJ.neg_mem hη
  obtain ⟨a₁, b₁, c₁, hab₁, hbc₁, hac₁, h₁, h₂⟩ :=
    ggD_exists_chain_of_meet hnegJ hab hcd (hγeq ▸ hγJ) (hγ'eq ▸ hγJ') hshare hne_supp
  let I : Finset (Fin k) := {a₁, b₁, c₁}
  have hIcard : I.card = 3 := Finset.card_eq_three.mpr ⟨a₁, b₁, c₁, hab₁, hac₁, hbc₁, rfl⟩
  have hIroots : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      Pi.single x (ε x) - Pi.single y (ε y) ∈ ggDMemberRoots e φ J :=
    ggD_single_sub_single_mem_of_chain hε hnegJ hΦJ.2 hab₁ hbc₁ hac₁ h₁ h₂
  obtain ⟨d, hdD, hdx⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers (xb : G) := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers (xb : G) from fun d hd => h d hd)
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hp := hpFact) (hBs.2 _ xb.2) hx1,
      pow_two] at h1
    have h2 : p * 2 ≤ p * p := Nat.mul_le_mul_left p hp.two_le
    have h3 := hp.two_le
    omega
  have hdC : d ∈ Subgroup.centralizer (J : Set G) := (Subgroup.mem_inf.mp (hDJ ▸ hdD)).2
  have hBBs : B ≤ Bs := hcfg.1.1.2.1.1
  let db : ↥Bs := ⟨d, hBBs (hDB hdD)⟩
  have hxε : ∀ a b, (ε a : ZMod p) * θ (Additive.ofMul xb) a =
      (ε b : ZMod p) * θ (Additive.ofMul xb) b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    obtain ⟨u, hu, -⟩ : Pi.single a (ε a) - Pi.single b (ε b) ∈ ggDMemberRoots e φ L := by
      rw [hΦL]
      exact ⟨a, b, hab, rfl⟩
    have h0 := (hfixθ u _ hu xb).mp ((hfx u _ hu).mpr (stdsub_dot_pair hε a b))
    rw [stdsub_sum_pair] at h0
    linear_combination h0
  have hconst : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (ε x : ZMod p) * θ (Additive.ofMul db) x =
      (ε y : ZMod p) * θ (Additive.ofMul db) y := by
    intro x hx y hy hxy
    obtain ⟨u, hu, huJ⟩ := hIroots x hx y hy hxy
    have hfixdb : ((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) db = db := by
      refine ggAutomizer_apply_eq_of_le_centralizer (fun j hj => ?_) huJ
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      exact (Subgroup.mem_centralizer_iff.mp hdC j hj).symm
    have h0 := (hfixθ u _ hu db).mp hfixdb
    rw [stdsub_sum_pair] at h0
    linear_combination h0
  have ha₀I : a₁ ∈ I := by simp [I]
  have hshift := ggDk_coord_shift hp θ hε (fun h => hx1 (by rw [h]; rfl)) hxε db
  obtain ⟨n, hn⟩ := hshift ((ε a₁ : ZMod p) * θ (Additive.ofMul db) a₁)
  let v : ↥Bs := db * (xb ^ n)⁻¹
  have hvI : ∀ a ∈ I, θ (Additive.ofMul v) a = 0 := by
    intro a ha
    rw [hn a]
    have hc : (ε a : ZMod p) * θ (Additive.ofMul db) a =
        (ε a₁ : ZMod p) * θ (Additive.ofMul db) a₁ := by
      by_cases haa : a = a₁
      · rw [haa]
      · exact hconst a ha a₁ ha₀I haa
    rw [hc, sub_self, mul_zero]
  have hvD : ((v : ↥Bs) : G) ∈ D := D.mul_mem hdD (D.inv_mem (D.pow_mem hxD n))
  have hvx : ((v : ↥Bs) : G) ∉ Subgroup.zpowers (xb : G) := fun h => hdx (by
    have h2 : d = ((v : ↥Bs) : G) * (xb : G) ^ n := by
      exact (inv_mul_cancel_right _ _).symm
    rw [h2]
    exact (Subgroup.zpowers _).mul_mem h (Subgroup.npow_mem_zpowers _ n))
  refine ⟨I, v, θ, hIcard, ?_, ?_, hIroots, hvI, ?_⟩
  ·
    exact (ggClosure_pair_eq hp hDcard hxD hvD hx1 (hBs.2 _ xb.2) hvx).symm
  ·
    have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hNN : Bs ≤ Subgroup.normalizer (L : Set G) :=
      GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1
    have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
      GGDichotomy.le_normalizer_stdSub hcomm hBBs hcfg.1.1.2.2.1 hNN
    have hel : ∀ b ∈ Bs, b ^ p = 1 := hBs.2
    have hmove : ∃ b : ↥Bs, r b ≠ b := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      have hall : Nat.card {b : ↥Bs // r b = b} = Nat.card ↥Bs :=
        Nat.card_congr (Equiv.subtypeUnivEquiv hcon)
      have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
      have := hrr.2
      rw [hall] at this
      have h1 : p = 1 := by
        have := Nat.eq_of_mul_eq_mul_left hpos (this.trans (mul_one _).symm)
        exact this
      exact hp.one_lt.ne' h1
    obtain ⟨b, hb⟩ := hmove
    obtain ⟨j, hjJ, hjN, hrj⟩ := mem_ggAutomizer_iff.mp hr
    have hbN : (b : G) ∈ Subgroup.normalizer (J : Set G) := hBsJ b.2
    set z : G := j * (b : G) * j⁻¹ * (b : G)⁻¹ with hz
    have hzJ : z ∈ J := by
      have h1 : (b : G) * j⁻¹ * (b : G)⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp hbN j⁻¹).mp (J.inv_mem hjJ)
      have h2 : z = j * ((b : G) * j⁻¹ * (b : G)⁻¹) := by simp [hz, mul_assoc]
      rw [h2]; exact J.mul_mem hjJ h1
    have hzB : z ∈ Bs := by
      have h1 : j * (b : G) * j⁻¹ ∈ Bs :=
        (Subgroup.mem_normalizer_iff.mp hjN (b : G)).mp b.2
      exact Bs.mul_mem h1 (Bs.inv_mem b.2)
    have hz1 : z ≠ 1 := by
      intro h
      apply hb
      apply Subtype.ext
      rw [hrj]
      have : j * (b : G) * j⁻¹ = (b : G) := by
        have := congrArg (· * (b : G)) h
        simpa [hz] using this
      exact this
    have hzp : z ^ p = 1 := hel z hzB
    have hord : orderOf z = p := orderOf_eq_prime (hp := hpFact) hzp hz1
    have := Subgroup.orderOf_dvd_natCard J hzJ
    rwa [hord] at this
  ·
    intro u η hu b
    rw [← hρu u]
    exact hθ (φ u) η hu b

end CFSG.StandardType

end
