
module

public import CFSG.Sporadic.Schreier.J4SInvolutionBase1

public import CFSG.Sporadic.Schreier.J4SInvCheck
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.Schreier.J4SLocalNodes
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SInvData
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.Schreier.J4SSylow

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native

@[expose] def ambElt (i : ℕ) : J :=
  (signedWord a b ambWords[i]!)⁻¹ *
    (nfElt (ambHead[i]!)[0]! (ambHead[i]!)[1]! *
      (signedWord a b ambWords[i]! * η (ambHead[i]!)[2]! * (signedWord a b ambWords[i]!)⁻¹)) ^
        hExp

theorem vS_conj_nf
    (n : ℕ) {e : ℕ} (he : e < 1024) :
    vS * nfElt n e * vS⁻¹ = nfElt (n ^^^ 4 ^^^ app11 elementColumns[e]! 4) e := by
  rw [vS, η_inv', nfElt, nfElt,
    show η 4 * (η n * uElt e) * η 4 = η 4 * η n * (uElt e * η 4 * (uElt e)⁻¹) * uElt e by group,
    uElt_acts he, ← η_xor, ← η_xor, Nat.xor_comm 4 n]

theorem kgen_inv_acts
    {i : ℕ} (hi : i < 4) : ActsBy (kgen i)⁻¹ genInvColumns[i]! := fun n => by
  rw [inv_inv]
  exact inv_conj_η_of_cols (kgen_acts hi) (genInv_all i hi) n

theorem uElt_conj_kgen
    {i e : ℕ} (hi : i < 4) (he : e < 1024) :
    kgen i * uElt e * (kgen i)⁻¹ = uElt ((conjTab[i]!)[e]!) := by
  obtain ⟨hlt, hcols⟩ := conj_all i hi e he
  refine eq_of_actsBy (K.mul_mem (K.mul_mem (kgen_mem_K i) (U_le_K (uElt_mem_U e)))
    (K.inv_mem (kgen_mem_K i))) (U_le_K (uElt_mem_U _)) ?_ (uElt_acts hlt)
  rw [hcols]
  exact actsBy_mul (actsBy_mul (kgen_acts hi) (uElt_acts he)) (kgen_inv_acts hi)

theorem kgen_conj_nf
    {i : ℕ} (hi : i < 4) (n : ℕ) {e : ℕ} (he : e < 1024) :
    kgen i * nfElt n e * (kgen i)⁻¹ =
      nfElt (app11 generatorColumns[i]! n) ((conjTab[i]!)[e]!) := by
  rw [nfElt, nfElt, show kgen i * (η n * uElt e) * (kgen i)⁻¹ =
      (kgen i * η n * (kgen i)⁻¹) * (kgen i * uElt e * (kgen i)⁻¹) by group,
    kgen_acts hi n, uElt_conj_kgen hi he]

theorem genElt_conj
    {g : ℕ} (hg : g < 5) (n : ℕ) {e : ℕ} (he : e < 1024) :
    genElt g * nfElt n e * (genElt g)⁻¹ = nfElt (genMapN g n e) (genMapE g e) := by
  unfold genElt genMapN genMapE
  split_ifs with h
  · exact vS_conj_nf n he
  · exact kgen_conj_nf (by omega) n he

section Generic

variable {G : Type*} [Group G]

end Generic

theorem rep_KPairs
    {i : ℕ} (hi : i < 4) : Rep Sp φ (kgen i) KPairs[i]! := by
  rw [KPairs_eq hi, kgen_def]
  exact rep_wordP (rep_x j4Facts.mat) (rep_y j4Facts.mat) _

theorem uElt_parent
    {e : ℕ} (he : e < 1024) (hpos : 0 < e) :
    uElt e = uElt (discoveryParents[e]!)[0]! * kgen (discoveryParents[e]!)[1]! := by
  obtain ⟨-, -, hpar, -⟩ := elem_all e he
  obtain ⟨hp, hg, heq⟩ := hpar hpos
  generalize (discoveryParents[e]!)[0]! = p at hp heq ⊢
  generalize (discoveryParents[e]!)[1]! = g at hg heq ⊢
  have h := actsBy_mul (uElt_acts (by omega : p < 1024)) (kgen_acts hg)
  rw [← heq] at h
  exact eq_of_actsBy (U_le_K (uElt_mem_U e)) (K.mul_mem (U_le_K (uElt_mem_U p)) (kgen_mem_K g))
    (uElt_acts he) h

theorem rep_uPairK :
    ∀ e < 1024, Rep Sp φ (uElt e) (uPairK KPairs e) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    rw [uPairK]
    split_ifs with h
    · rw [uElt_parent he h.1]
      have hg := ((elem_all e he).2.2.1 h.1).2.1
      exact rep_mulP (ih _ h.2 (by omega)) (rep_KPairs hg)
    · have he0 : e = 0 := by
        by_contra hne
        exact h ⟨Nat.pos_of_ne_zero hne, ((elem_all e he).2.2.1 (Nat.pos_of_ne_zero hne)).1⟩
      subst he0
      rw [uElt_zero]
      exact rep_oneP

theorem rep_nfElt
    (n : ℕ) {e : ℕ} (he : e < 1024) :
    Rep Sp φ (nfElt n e) (mulP (etaP n) (uPairK KPairs e)) :=
  rep_mulP (rep_etaP j4Facts.mat n) (rep_uPairK e he)

theorem rep_ambElt
    {i : ℕ} (hi : i < 77) : Rep Sp φ (ambElt i) (ambConj KPairs i) := by
  have hw := rep_wordP (rep_a j4Facts.mat) (rep_b j4Facts.mat) (ambWords[i]!)
  have ha := rep_nfElt (ambHead[i]!)[0]! (amb_lt i hi).2
  exact rep_mulP (rep_invP hw) (rep_powP (rep_mulP ha (rep_mulP (rep_mulP hw
    (rep_etaP j4Facts.mat _)) (rep_invP hw))) hExp)

theorem ambElt_conj
    {i : ℕ} (hi : i < 77) :
    ambElt i * nfElt (ambHead[i]!)[0]! (ambHead[i]!)[1]! * (ambElt i)⁻¹ =
        η (ambHead[i]!)[2]! ∧
      ((ambHead[i]!)[2]! = 1 ∨ (ambHead[i]!)[2]! = 14) := by
  have hc : ambCheck KPairs i = true := by
    have h := ambAll_eq
    unfold ambAllOK at h
    exact List.all_eq_true.1 h i (List.mem_range.2 hi)
  unfold ambCheck at hc
  rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hc
  refine ⟨eq_of_rep (rep_mulP (rep_mulP (rep_ambElt hi) (rep_nfElt _ (amb_lt i hi).2))
    (rep_invP (rep_ambElt hi))) (rep_etaP j4Facts.mat _) hc.1, hc.2⟩

theorem root_conj
    {n e : ℕ} (hn : n < 2048) (hne : ¬ (n = 0 ∧ e = 0))
    (hcase : e = 0 ∨ ambIdx n e < 77) :
    ∃ c : J, c * nfElt n e * c⁻¹ = η 1 ∨ c * nfElt n e * c⁻¹ = η 14 := by
  rcases hcase with rfl | hamb
  · have h0 : n ≠ 0 := fun h => hne ⟨h, rfl⟩
    have hη : η n ≠ 1 := fun h => h0 (η_injOn hn (by norm_num) (h.trans η_zero.symm))
    have hnf : nfElt n 0 = η n := by rw [nfElt, uElt_zero, mul_one]
    rw [hnf]
    rcases QT_unique_J4_local_normal_module_irreducible.1 (η n) (η_mem_N n) with h | h | h
    · exact absurd h hη
    · obtain ⟨k, -, hk⟩ := h
      exact ⟨k⁻¹, Or.inl (by rw [hk]; group)⟩
    · obtain ⟨k, -, hk⟩ := h
      exact ⟨k⁻¹, Or.inr (by rw [hk]; group)⟩
  · obtain ⟨h1, h2⟩ := ambIdx_spec hamb
    obtain ⟨hc, hs⟩ := ambElt_conj hamb
    rw [h1, h2] at hc
    rcases hs with hs | hs
    · exact ⟨ambElt (ambIdx n e), Or.inl (by rw [hc, hs])⟩
    · exact ⟨ambElt (ambIdx n e), Or.inr (by rw [hc, hs])⟩

theorem invPair_of_mem_S0
    {t : J} (ht : t ∈ S0) (h2 : orderOf t = 2) :
    ∃ n e : ℕ, (n < 2048 ∧ e < 1024 ∧ squares[e]! = 0 ∧ app11 elementColumns[e]! n = n ∧
      ¬ (n = 0 ∧ e = 0)) ∧ t = nfElt n e := by
  obtain ⟨p, hp⟩ := nfMap_bijective.2 ⟨t, ht⟩
  have htp : t = nfElt p.1 p.2 := (congrArg Subtype.val hp).symm
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rw [h2] at h
    exact h
  have hsq : nfElt p.1 p.2 * nfElt p.1 p.2 = 1 := by rw [← htp, ← sq]; exact ht2
  rw [nfElt_sq p.2.isLt] at hsq
  obtain ⟨hl1, hl2⟩ := stepNF_lt p.1.isLt p.2.isLt
  obtain ⟨hs1, hs2⟩ := (nfElt_eq_one_iff hl1 hl2).1 hsq
  rw [stepNF] at hs1 hs2
  dsimp only at hs1 hs2
  refine ⟨p.1, p.2, ⟨p.1.isLt, p.2.isLt, hs2, (xor_eq_zero_iff.1 hs1).symm, ?_⟩, htp⟩
  rintro ⟨h1, h2'⟩
  have h1' : nfElt p.1 p.2 = 1 := by
    rw [h1, h2']
    exact (nfElt_eq_one_iff (by norm_num) (by norm_num)).2 ⟨rfl, rfl⟩
  rw [← htp] at h1'
  rw [h1', orderOf_one] at h2
  omega

theorem mem_forest
    {t : J} (ht : t ∈ S0) (ho : orderOf t = 2) :
    ∃ j < 19967, t = nfElt (fN j) (fE j) := by
  obtain ⟨n, e, ⟨hn, he, hsq, hfix, hne⟩, hnf⟩ := invPair_of_mem_S0 ht ho
  obtain ⟨hj, hjn, hje⟩ := forest_complete e he n hn ⟨hsq, hfix, hne⟩
  refine ⟨_, hj, ?_⟩
  rw [hjn, hje]
  exact hnf

theorem CTU_J4_every_inner_involution_conjugate_into_local_binary_subgroup :
    ∀ t : J, orderOf t = 2 →
      (∃ g : J, g * t * g⁻¹ ∈ N ∧ g * t * g⁻¹ ≠ 1) ∧
        ∃ g : J, g * t * g⁻¹ = η 1 ∨ g * t * g⁻¹ = η 14 := by
  intro t ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := fusion_of_forest S0 nfElt genElt fN fE fP fG genMapN genMapE
    (fun r => fE r = 0 ∨ ambIdx (fN r) (fE r) < 77) 19967 (η 1) (η 14)
    (fun t ht => by
      have hP : IsPGroup 2 (Subgroup.zpowers t) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
      obtain ⟨g, hg⟩ := exists_conj_mem_sylow S0Sylow hP
      rw [S0Sylow_coe] at hg
      exact ⟨g, hg⟩)
    (fun t ht ho => mem_forest ht ho)
    (fun g hg => genElt_mem hg)
    (fun g hg p hp => genElt_conj hg (fN p) (forest_all p hp).1.2.1)
    (fun j hj => (forest_all j hj).2)
    (fun r hr hroot => root_conj (forest_all r hr).1.1 (forest_all r hr).1.2.2.2.2 hroot) t ht
  refine ⟨?_, key⟩
  obtain ⟨g, hg⟩ := key
  refine ⟨g, ?_, ?_⟩
  · rcases hg with hg | hg <;> rw [hg] <;> exact η_mem_N _
  · rcases hg with hg | hg <;> rw [hg] <;> intro h
    · exact absurd (η_injOn (k := 0) (by norm_num) (by norm_num) (h.trans η_zero.symm))
        (by norm_num)
    · exact absurd (η_injOn (k := 0) (by norm_num) (by norm_num) (h.trans η_zero.symm))
        (by norm_num)

end CFSG.Sporadic.J4Schreier
