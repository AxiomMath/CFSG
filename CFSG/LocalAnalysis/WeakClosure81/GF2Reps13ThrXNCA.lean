module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXNB
public import CFSG.LocalAnalysis.GLTheoremA.Lemma48
public import CFSG.LocalAnalysis.GLTheoremA.S3.KMBasic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXNA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

variable {A Q O : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16n_Q_isPGroup (h : HNon A Q O t) : IsPGroup 3 ↥Q := by
  intro q
  exact ⟨1, by rw [pow_one]; exact Subtype.ext (h.hQe.2 (q : MulAut W) q.2)⟩

private theorem w16n_Q_card_pow (h : HNon A Q O t) : ∃ d : ℕ, Nat.card ↥Q = 3 ^ d := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact (w16n_Q_isPGroup h).exists_card_eq

private theorem w16n_Q_odd (h : HNon A Q O t) : Odd (Nat.card ↥Q) := by
  obtain ⟨d, hd⟩ := w16n_Q_card_pow h
  rw [hd]
  exact Odd.pow (by norm_num : Odd 3)

private theorem w16n_commSub_ne_bot (h : HNon A Q O t) : commSub ⊤ Q ≠ ⊥ := by
  intro hbot
  apply h.hQ1
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  apply MulEquiv.ext
  intro w
  exact (mem_fixV.mp ((commSub_eq_bot_iff.mp hbot) (Subgroup.mem_top w))) q hq

private theorem w16n_comps_nonempty (h : HNon A Q O t) : (s13IsoComps Q).Nonempty := by
  have hsup := iSup_s13IsoComps h.hW (w16n_Q_odd h)
  by_contra hemp
  apply w16n_commSub_ne_bot h
  rw [← hsup]
  rw [Set.not_nonempty_iff_eq_empty.mp hemp]
  simp

private theorem w16n_card_le (h : HNon A Q O t) :
    Nat.card ↥Q ≤ 3 ^ (s13IsoComps Q).ncard := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨lam, hl⟩ := exists_coord h.hW hp3 hp32 h.hQe
  let f : ↥Q → (s13IsoComps Q → ZMod 3) := fun x U => lam U (Additive.ofMul x)
  have hf : Function.Injective f := by
    intro x y hxy
    refine coord_injective h.hW hp3 hp32 h.hQe hl ?_
    intro U
    exact congrFun hxy U
  have h1 := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_coe_set_eq] at h1

private theorem w16n_rank_two_commute_conj (h : HNon A Q O t) {g : MulAut W} (hg : g ∈ A)
    {R S : Subgroup (MulAut W)} (hR : R ≤ Q) (hS : S ≤ Q)
    (hrR : rk ↥(commSub ⊤ R) = 2) (hrS : rk ↥(commSub ⊤ S) = 2) :
    ⁅R, S.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hOmap : S.map (MulAut.conj g).toMonoidHom ≤ O := by
    refine (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hS).trans ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact h.hOA g hg y (h.hQO hy)
  refine w16g_rank_two_commute h.hW h.hO3 (hR.trans h.hQO) hOmap hrR ?_
  have hmap := CFSG.RankThree.S4Free.Stell.map_commSub g ⊤ S
  rw [Subgroup.map_top_of_surjective _ g.surjective] at hmap
  rw [← hmap, CFSG.RankThree.S4Free.Stell.rk_map_mulAut]
  exact hrS

private theorem w16n_not_gen_rank_two (h : HNon A Q O t) :
    ¬ ((⨆ (R : {R : Subgroup (MulAut W) // R ≤ Q ∧ rk ↥(commSub ⊤ R) = 2}),
        (R : Subgroup (MulAut W))) = Q) := by
  intro hgen
  obtain ⟨g, hgA, hnc⟩ := h.hnc
  apply hnc
  rw [hgen.symm, Subgroup.map_iSup]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup_le fun i => ?_
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  refine Subgroup.iSup_induction
    (fun j : {R : Subgroup (MulAut W) // R ≤ Q ∧ rk ↥(commSub ⊤ R) = 2} =>
      (j : Subgroup (MulAut W)).map (MulAut.conj g).toMonoidHom)
    (C := fun s => s * r = r * s) hs ?_ ?_ ?_
  · intro j s hs
    have hcomm := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (w16n_rank_two_commute_conj h hgA i.2.1 j.2.1 i.2.2 j.2.2)) hr
    rw [Subgroup.mem_centralizer_iff] at hcomm
    exact hcomm s hs
  · simp
  · intro a b ha hb
    calc a * b * r = a * (b * r) := by rw [mul_assoc]
      _ = a * (r * b) := by rw [hb]
      _ = (a * r) * b := by rw [mul_assoc]
      _ = (r * a) * b := by rw [ha]
      _ = r * (a * b) := by rw [mul_assoc]

private theorem w16n_not_le_gen (h : HNon A Q O t) :
    ¬ Q ≤ ⨆ (R : {R : Subgroup (MulAut W) // R ≤ Q ∧ rk ↥(commSub ⊤ R) = 2}),
        (R : Subgroup (MulAut W)) := by
  intro hle
  apply w16n_not_gen_rank_two h
  exact (le_antisymm hle (iSup_le fun
    (R : {R : Subgroup (MulAut W) // R ≤ Q ∧ rk ↥(commSub ⊤ R) = 2}) => R.2.1)).symm

private theorem w16n_conj_isPGroup (h : HNon A Q O t) (g : MulAut W) :
    IsPGroup 3 ↥(Q.map (MulAut.conj g).toMonoidHom) := by
  intro x
  obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp x.2
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (by
    show ((x : MulAut W)) ^ 3 = 1
    rw [← hqeq]
    change ((MulAut.conj g) q) ^ 3 = 1
    rw [← map_pow, h.hQe.2 q hq, map_one])

private theorem w16n_card_ne_three (h : HNon A Q O t) : Nat.card ↥Q ≠ 3 := by
  intro hcard
  obtain ⟨g, hgA, hnc⟩ := h.hnc
  apply hnc
  have hQ'O : Q.map (MulAut.conj g).toMonoidHom ≤ O := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact h.hOA g hgA y (h.hQO hy)
  have hPZ : Q.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (Q : Set (MulAut W)) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    exact h.hQN x (hQ'O hx) y hy
  have hcent := CFSG.LocalAnalysis.GLTheoremA.le_centralizer_of_isPGroup_of_card_eq
    (p := 3) (by norm_num) (w16n_conj_isPGroup h g) hcard hPZ
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hcent


private theorem w16n_conj_mem_centSub_map_iff (U : Subgroup W) (g : MulAut W) (y : MulAut W) :
    g * y * g⁻¹ ∈ centSub (U.map g.toMonoidHom) ↔ y ∈ centSub U := by
  rw [mem_centSub, mem_centSub]
  constructor
  · intro hh u hu
    have hgu : g u ∈ U.map g.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have h1 : (g * y * g⁻¹) (g u) = g u := hh (g u) hgu
    have h2 : (g * y * g⁻¹) (g u) = g (y u) := by simp [MulAut.mul_apply]
    rw [h2] at h1
    exact g.injective h1
  · intro hh u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    have hv' : y v = v := hh v hv
    simp [MulAut.mul_apply, hv']

private theorem w16n_kerOn_map_eq (h : HNon A Q O t) {x : MulAut W} (hxO : x ∈ O)
    {U : Subgroup W} (hU : U ∈ s13IsoComps Q) :
    s13KerOn Q (U.map x.toMonoidHom) = (s13KerOn Q U).map (MulAut.conj x).toMonoidHom := by
  ext z
  constructor
  · intro hz
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * z * x, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact h.hQN x⁻¹ (O.inv_mem hxO) z hz.1
      · have hzeq : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
        have hz' : x * (x⁻¹ * z * x) * x⁻¹ ∈ centSub (U.map x.toMonoidHom) := by
          rw [hzeq]; exact hz.2
        exact (w16n_conj_mem_centSub_map_iff U x (x⁻¹ * z * x)).mp hz'
    · change x * (x⁻¹ * z * x) * x⁻¹ = z
      group
  · intro hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    rw [← hyz]
    exact ⟨h.hQN x hxO y hy.1, (w16n_conj_mem_centSub_map_iff U x y).mpr hy.2⟩

private theorem w16n_all_ker_eq_bot (h : HNon A Q O t) :
    ∀ x ∈ Q, (∀ U ∈ s13IsoComps Q, x ∈ s13KerOn Q U) → x = 1 := by
  intro x hx hker
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨lam, hl⟩ := exists_coord h.hW hp3 hp32 h.hQe
  have h := coord_injective h.hW hp3 hp32 h.hQe hl (x := ⟨x, hx⟩) (y := 1) (by
    intro U
    have hx0 : lam U (Additive.ofMul (⟨x, hx⟩ : ↥Q)) = 0 := ((hl U).2 _).mpr (hker U U.2)
    have h10 : lam U (Additive.ofMul (1 : ↥Q)) = 0 := ((hl U).2 _).mpr (Subgroup.one_mem _)
    rw [hx0, h10])
  exact Subtype.ext_iff.mp h

private theorem w16n_rk_of_supp_singleton (h : HNon A Q O t) {U : Subgroup W}
    (hU : U ∈ s13IsoComps Q) {R : Subgroup (MulAut W)} (hRQ : R ≤ Q)
    (hsupp : s13Supp Q R = {U}) : rk ↥(commSub ⊤ R) = rk ↥U := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  rw [rk_commSub_top_eq_sum h.hW hp3 hp32 h.hQe hRQ, hsupp, finsum_mem_singleton]

private theorem w16n_sum_le_of_two_le {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hcard : Nat.card ι = 3) (h2 : ∀ i, 2 ≤ f i) (h6 : ∑ i, f i ≤ 6) :
    ∀ i, f i = 2 := by
  classical
  intro i
  have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hsplit : f i + ∑ j ∈ (Finset.univ : Finset ι).erase i, f j = ∑ j, f j :=
    Finset.add_sum_erase _ f hmem
  have hcard_erase : ((Finset.univ : Finset ι).erase i).card = 2 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  have hb : 2 * 2 ≤ ∑ j ∈ (Finset.univ : Finset ι).erase i, f j := by
    calc 2 * 2 = ∑ j ∈ (Finset.univ : Finset ι).erase i, 2 := by
          rw [Finset.sum_const, hcard_erase, Nat.nsmul_eq_mul]
      _ ≤ ∑ j ∈ (Finset.univ : Finset ι).erase i, f j :=
          Finset.sum_le_sum fun j _ => h2 j
  have hmain : f i + 4 ≤ 6 := by
    calc f i + 4 = f i + 2 * 2 := by norm_num
      _ ≤ f i + ∑ j ∈ (Finset.univ : Finset ι).erase i, f j := add_le_add le_rfl hb
      _ = ∑ j, f j := hsplit
      _ ≤ 6 := h6
  have h2i : 2 ≤ f i := h2 i
  omega

private theorem w16n_ranks_eq_two_of_ncard_three (h : HNon A Q O t)
    (hcard : (s13IsoComps Q).ncard = 3) :
    ∀ U ∈ s13IsoComps Q, rk ↥U = 2 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  classical
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  haveI : Fintype {U : Subgroup W // U ∈ s13IsoComps Q} := Fintype.ofFinite _
  have hsum : (∑ i : {U : Subgroup W // U ∈ s13IsoComps Q}, rk ↥(i.1)) ≤ 6 := by
    have h := (w16n_components h).2.1
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype] at h
    exact h
  have h2rk : ∀ i : {U : Subgroup W // U ∈ s13IsoComps Q}, 2 ≤ rk ↥(i.1) := by
    intro i
    obtain ⟨s, hs, hsrk⟩ := rk_s13IsoComps_eq h.hW hp3 hp32 h.hQe i.2
    have hd3 : dParam 3 = 2 := by
      rw [dParam]
      exact orderOf_eq_prime (p := 2) (by decide) (by decide)
    rw [hd3] at hsrk
    omega
  have hcardN : Nat.card {U : Subgroup W // U ∈ s13IsoComps Q} = 3 := by
    rw [Nat.card_coe_set_eq, hcard]
  have hbound := w16n_sum_le_of_two_le (fun i : {U : Subgroup W // U ∈ s13IsoComps Q} =>
    rk ↥(i.1)) hcardN h2rk hsum
  intro U hU
  exact hbound ⟨U, hU⟩

private theorem w16n_map_fixed_of_two (h : HNon A Q O t) {x : MulAut W} (hxO : x ∈ O)
    (hx3 : x ^ 3 = 1) {U U' : Subgroup W} (hU : U ∈ s13IsoComps Q)
    (hU' : U' ∈ s13IsoComps Q) (hne : U ≠ U') (hS : s13IsoComps Q = {U, U'}) :
    U.map x.toMonoidHom = U := by
  have hnorm : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := fun y hy => h.hQN x hxO y hy
  have hnorm' : ∀ y ∈ Q, x⁻¹ * y * x ∈ Q := fun y hy =>
    h.hQN x⁻¹ (O.inv_mem hxO) y hy
  have hA : U.map x.toMonoidHom ∈ s13IsoComps Q := map_mem_s13IsoComps hnorm hnorm' hU
  have hB : (U.map x.toMonoidHom).map x.toMonoidHom ∈ s13IsoComps Q :=
    map_mem_s13IsoComps hnorm hnorm' hA
  have hchain : ((U.map x.toMonoidHom).map x.toMonoidHom).map x.toMonoidHom
      = U.map (x ^ 3).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hC : ((U.map x.toMonoidHom).map x.toMonoidHom).map x.toMonoidHom = U := by
    rw [hchain, hx3]
    exact Subgroup.map_id U
  rw [hS] at hA hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
  rcases hA with hA | hA
  · exact hA
  · exfalso
    rcases hB with hB | hB
    · have hA' : U'.map x.toMonoidHom = U :=
        (congrArg (fun S : Subgroup W => S.map x.toMonoidHom) hA.symm).trans hB
      have hC' : ((U.map x.toMonoidHom).map x.toMonoidHom).map x.toMonoidHom = U' := by
        rw [hA, hA', hA]
      exact hne (hC'.symm.trans hC).symm
    · have hA' : U'.map x.toMonoidHom = U' :=
        (congrArg (fun S : Subgroup W => S.map x.toMonoidHom) hA.symm).trans hB
      have hC' : ((U.map x.toMonoidHom).map x.toMonoidHom).map x.toMonoidHom = U' := by
        rw [hA, hA', hA']
      exact hne (hC'.symm.trans hC).symm

private theorem w16n_ncard_ne_two (h : HNon A Q O t) : (s13IsoComps Q).ncard ≠ 2 := by
  intro hcard2
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨U1, U2, hne, hSeq⟩ := Set.ncard_eq_two.mp hcard2
  have hU1 : U1 ∈ s13IsoComps Q := by rw [hSeq]; simp
  have hU2 : U2 ∈ s13IsoComps Q := by rw [hSeq]; simp
  obtain ⟨d, hd⟩ := w16n_Q_card_pow h
  have hdle : d ≤ 2 := by
    have hle := w16n_card_le h
    rw [hd, hcard2] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have hdne0 : d ≠ 0 := by
    intro hd0
    exact h.hQ1 (Subgroup.card_eq_one.mp (by rw [hd, hd0]; norm_num))
  have hdne1 : d ≠ 1 := by
    intro hd1
    exact w16n_card_ne_three h (by rw [hd, hd1]; norm_num)
  have hd2 : d = 2 := by omega
  have hcardQ : Nat.card ↥Q = 9 := by rw [hd, hd2]; norm_num
  obtain ⟨g, hgA, hnc⟩ := h.hnc
  let Q' : Subgroup (MulAut W) := Q.map (MulAut.conj g).toMonoidHom
  have hQ'O : Q' ≤ O := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact h.hOA g hgA y (h.hQO hy)
  have hx3 : ∀ x ∈ Q', x ^ 3 = 1 := by
    intro x hx
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hx
    rw [← hqeq]
    change ((MulAut.conj g) q) ^ 3 = 1
    rw [← map_pow, h.hQe.2 q hq, map_one]
  have hH1mem := s13KerOn_mem_hyperplanes h.hW hp3 hp32 h.hQe hU1
  have hH2mem := s13KerOn_mem_hyperplanes h.hW hp3 hp32 h.hQe hU2
  have hH1card : Nat.card ↥(s13KerOn Q U1) = 3 := by
    have hm := Subgroup.relIndex_mul_card (H := s13KerOn Q U1) (K := Q)
    rw [inf_eq_left.mpr hH1mem.1, hH1mem.2, hcardQ] at hm
    omega
  have hH2card : Nat.card ↥(s13KerOn Q U2) = 3 := by
    have hm := Subgroup.relIndex_mul_card (H := s13KerOn Q U2) (K := Q)
    rw [inf_eq_left.mpr hH2mem.1, hH2mem.2, hcardQ] at hm
    omega
  have hHne : s13KerOn Q U1 ≠ s13KerOn Q U2 := fun heq =>
    hne ((w16n_components h).1 U1 hU1 U2 hU2 heq)
  have hHsup : s13KerOn Q U1 ⊔ s13KerOn Q U2 = Q := by
    have hle : s13KerOn Q U1 ⊔ s13KerOn Q U2 ≤ Q := sup_le hH1mem.1 hH2mem.1
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hdvd : Nat.card ↥(s13KerOn Q U1 ⊔ s13KerOn Q U2) ∣ 9 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [hcardQ] at this
    have hge : 3 ≤ Nat.card ↥(s13KerOn Q U1 ⊔ s13KerOn Q U2) := by
      have hd := Subgroup.card_dvd_of_le
        (show s13KerOn Q U1 ≤ s13KerOn Q U1 ⊔ s13KerOn Q U2 from le_sup_left)
      rw [hH1card] at hd
      exact Nat.le_of_dvd Nat.card_pos hd
    have hne3 : Nat.card ↥(s13KerOn Q U1 ⊔ s13KerOn Q U2) ≠ 3 := by
      intro h3
      have heq : s13KerOn Q U1 = s13KerOn Q U1 ⊔ s13KerOn Q U2 :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hH1card])
      have hle21 : s13KerOn Q U2 ≤ s13KerOn Q U1 := by
        rw [heq]; exact le_sup_right
      exact hHne (Subgroup.eq_of_le_of_card_ge hle21 (by rw [hH1card, hH2card])).symm
    have hdvd' : Nat.card ↥(s13KerOn Q U1 ⊔ s13KerOn Q U2) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 from by norm_num]; exact hdvd
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp3).1 hdvd'
    have hk_eq : k = 2 := by
      interval_cases k
      · rw [hk] at hge; norm_num at hge
      · exact absurd (show Nat.card ↥(s13KerOn Q U1 ⊔ s13KerOn Q U2) = 3 by rw [hk]; norm_num) hne3
      · rfl
    rw [hk, hk_eq, hcardQ]
    norm_num
  have hfix1 : ∀ x ∈ Q', U1.map x.toMonoidHom = U1 := fun x hx =>
    w16n_map_fixed_of_two h (hQ'O hx) (hx3 x hx) hU1 hU2 hne hSeq
  have hfix2 : ∀ x ∈ Q', U2.map x.toMonoidHom = U2 := fun x hx =>
    w16n_map_fixed_of_two h (hQ'O hx) (hx3 x hx) hU2 hU1 hne.symm (by rw [hSeq, Set.pair_comm])
  have hnormH1 : Q' ≤ Subgroup.normalizer (s13KerOn Q U1 : Set (MulAut W)) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hxO : x ∈ O := hQ'O hx
    have hmap : s13KerOn Q (U1.map x.toMonoidHom) = s13KerOn Q U1 := by rw [hfix1 x hx]
    have hconj : (MulAut.conj x) y ∈ s13KerOn Q U1 := by
      rw [← hmap, w16n_kerOn_map_eq h hxO hU1]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hconj
  have hnormH2 : Q' ≤ Subgroup.normalizer (s13KerOn Q U2 : Set (MulAut W)) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hxO : x ∈ O := hQ'O hx
    have hmap : s13KerOn Q (U2.map x.toMonoidHom) = s13KerOn Q U2 := by rw [hfix2 x hx]
    have hconj : (MulAut.conj x) y ∈ s13KerOn Q U2 := by
      rw [← hmap, w16n_kerOn_map_eq h hxO hU2]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hconj
  have hcent1 : Q' ≤ Subgroup.centralizer (s13KerOn Q U1 : Set (MulAut W)) :=
    CFSG.LocalAnalysis.GLTheoremA.le_centralizer_of_isPGroup_of_card_eq (p := 3) (by norm_num)
      (w16n_conj_isPGroup h g) hH1card hnormH1
  have hcent2 : Q' ≤ Subgroup.centralizer (s13KerOn Q U2 : Set (MulAut W)) :=
    CFSG.LocalAnalysis.GLTheoremA.le_centralizer_of_isPGroup_of_card_eq (p := 3) (by norm_num)
      (w16n_conj_isPGroup h g) hH2card hnormH2
  have hle1 : s13KerOn Q U1 ≤ Subgroup.centralizer (Q' : Set (MulAut W)) :=
    Subgroup.le_centralizer_iff.mp hcent1
  have hle2 : s13KerOn Q U2 ≤ Subgroup.centralizer (Q' : Set (MulAut W)) :=
    Subgroup.le_centralizer_iff.mp hcent2
  have hleQ : Q ≤ Subgroup.centralizer (Q' : Set (MulAut W)) := by
    rw [← hHsup]
    exact sup_le hle1 hle2
  have hc : Q' ≤ Subgroup.centralizer (Q : Set (MulAut W)) :=
    Subgroup.le_centralizer_iff.mp hleQ
  apply hnc
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hc


private theorem w16n_supp_of_le_ker (h : HNon A Q O t) {U : Subgroup W}
    (hU : U ∈ s13IsoComps Q) {R : Subgroup (MulAut W)} (hRQ : R ≤ Q)
    (hRle : ∀ U' ∈ s13IsoComps Q, U' ≠ U → R ≤ s13KerOn Q U')
    (hRnot : ¬ R ≤ s13KerOn Q U) : s13Supp Q R = {U} := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  ext U'
  constructor
  · intro hU'
    rw [s13Supp, Set.mem_setOf_eq] at hU'
    by_contra hne
    have hbot : commSub U' R = ⊥ :=
      (s13IsoComps_commSub_eq h.hW hp3 hp32 h.hQe hRQ hU'.1).1 (hRle U' hU'.1 hne)
    exact hU'.2 hbot
  · intro hU'
    rw [Set.mem_singleton_iff] at hU'
    subst hU'
    refine ⟨hU, ?_⟩
    rw [(s13IsoComps_commSub_eq h.hW hp3 hp32 h.hQe hRQ hU).2 hRnot]
    exact (s13IsoComps_le_commSub h.hW (w16n_Q_odd h) hU).1

private theorem w16n_sup_eq_Q (hcardQ : Nat.card ↥Q = 27) {H R : Subgroup (MulAut W)}
    (hH : H ≤ Q) (hHR : R ≤ Q) (hHcard : Nat.card ↥H = 9) (hRcard : 3 ≤ Nat.card ↥R)
    (hnot : ¬ R ≤ H) : H ⊔ R = Q := by
  have hle : H ⊔ R ≤ Q := sup_le hH hHR
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hdvd : Nat.card ↥(H ⊔ R) ∣ 27 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hcardQ] at this
  have hge : 9 ≤ Nat.card ↥(H ⊔ R) := by
    have hd := Subgroup.card_dvd_of_le (show H ≤ H ⊔ R from le_sup_left)
    rw [hHcard] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have hne9 : Nat.card ↥(H ⊔ R) ≠ 9 := by
    intro h9
    have heq : H = H ⊔ R := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h9, hHcard])
    exact hnot (by rw [heq]; exact le_sup_right)
  have hdvd' : Nat.card ↥(H ⊔ R) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 from by norm_num]; exact hdvd
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1 hdvd'
  have hk_eq : k = 3 := by
    interval_cases k
    · rw [hk] at hge; norm_num at hge
    · rw [hk] at hge; norm_num at hge
    · exact absurd (show Nat.card ↥(H ⊔ R) = 9 by rw [hk]; norm_num) hne9
    · rfl
  rw [hk, hk_eq, hcardQ]
  norm_num

private theorem w16n_not_three_three (h : HNon A Q O t) :
    ¬ ((s13IsoComps Q).ncard = 3 ∧ Nat.card ↥Q = 27) := by
  rintro ⟨hS3, hcardQ⟩
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨U1, U2, U3, h12, h13, h23, hSeq⟩ := Set.ncard_eq_three.mp hS3
  have hU1 : U1 ∈ s13IsoComps Q := by rw [hSeq]; simp
  have hU2 : U2 ∈ s13IsoComps Q := by rw [hSeq]; simp
  have hU3 : U3 ∈ s13IsoComps Q := by rw [hSeq]; simp
  have hrk : ∀ U ∈ s13IsoComps Q, rk ↥U = 2 := w16n_ranks_eq_two_of_ncard_three h hS3
  have hH1 := s13KerOn_mem_hyperplanes h.hW hp3 hp32 h.hQe hU1
  have hH2 := s13KerOn_mem_hyperplanes h.hW hp3 hp32 h.hQe hU2
  have hH3 := s13KerOn_mem_hyperplanes h.hW hp3 hp32 h.hQe hU3
  have hH1card : Nat.card ↥(s13KerOn Q U1) = 9 := by
    have hm := Subgroup.relIndex_mul_card (H := s13KerOn Q U1) (K := Q)
    rw [inf_eq_left.mpr hH1.1, hH1.2, hcardQ] at hm
    omega
  have hH2card : Nat.card ↥(s13KerOn Q U2) = 9 := by
    have hm := Subgroup.relIndex_mul_card (H := s13KerOn Q U2) (K := Q)
    rw [inf_eq_left.mpr hH2.1, hH2.2, hcardQ] at hm
    omega
  have hH3card : Nat.card ↥(s13KerOn Q U3) = 9 := by
    have hm := Subgroup.relIndex_mul_card (H := s13KerOn Q U3) (K := Q)
    rw [inf_eq_left.mpr hH3.1, hH3.2, hcardQ] at hm
    omega
  have hHne12 : s13KerOn Q U1 ≠ s13KerOn Q U2 := fun heq =>
    h12 ((w16n_components h).1 U1 hU1 U2 hU2 heq)
  have hHne13 : s13KerOn Q U1 ≠ s13KerOn Q U3 := fun heq =>
    h13 ((w16n_components h).1 U1 hU1 U3 hU3 heq)
  have hHne23 : s13KerOn Q U2 ≠ s13KerOn Q U3 := fun heq =>
    h23 ((w16n_components h).1 U2 hU2 U3 hU3 heq)
  have hAc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.hQe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hishyp2 : CFSG.LocalAnalysis.GLTheoremA.S3.KM.IsHyp 3 Q (s13KerOn Q U2) := by
    refine ⟨hH2.1, ?_⟩
    have hm := Subgroup.relIndex_mul_card (H := s13KerOn Q U2) (K := Q)
    rw [inf_eq_left.mpr hH2.1, hH2.2] at hm
    omega
  have hishyp3 : CFSG.LocalAnalysis.GLTheoremA.S3.KM.IsHyp 3 Q (s13KerOn Q U3) := by
    refine ⟨hH3.1, ?_⟩
    have hm := Subgroup.relIndex_mul_card (H := s13KerOn Q U3) (K := Q)
    rw [inf_eq_left.mpr hH3.1, hH3.2] at hm
    omega
  have hR1card : Nat.card ↥(s13KerOn Q U2 ⊓ s13KerOn Q U3) = 3 := by
    have hm := CFSG.LocalAnalysis.GLTheoremA.S3.KM.IsHyp.card_inf hp3 hAc hishyp2 hishyp3 hHne23
    rw [hcardQ, show (3 : ℕ) ^ 2 = 9 from by norm_num] at hm
    nlinarith [hm]
  have hR2card : Nat.card ↥(s13KerOn Q U1 ⊓ s13KerOn Q U3) = 3 := by
    have hishyp1 : CFSG.LocalAnalysis.GLTheoremA.S3.KM.IsHyp 3 Q (s13KerOn Q U1) := by
      refine ⟨hH1.1, ?_⟩
      have hm := Subgroup.relIndex_mul_card (H := s13KerOn Q U1) (K := Q)
      rw [inf_eq_left.mpr hH1.1, hH1.2] at hm
      omega
    have hm := CFSG.LocalAnalysis.GLTheoremA.S3.KM.IsHyp.card_inf hp3 hAc hishyp1 hishyp3 hHne13
    rw [hcardQ, show (3 : ℕ) ^ 2 = 9 from by norm_num] at hm
    nlinarith [hm]
  have hR3card : Nat.card ↥(s13KerOn Q U1 ⊓ s13KerOn Q U2) = 3 := by
    have hishyp1 : CFSG.LocalAnalysis.GLTheoremA.S3.KM.IsHyp 3 Q (s13KerOn Q U1) := by
      refine ⟨hH1.1, ?_⟩
      have hm := Subgroup.relIndex_mul_card (H := s13KerOn Q U1) (K := Q)
      rw [inf_eq_left.mpr hH1.1, hH1.2] at hm
      omega
    have hm := CFSG.LocalAnalysis.GLTheoremA.S3.KM.IsHyp.card_inf hp3 hAc hishyp1 hishyp2 hHne12
    rw [hcardQ, show (3 : ℕ) ^ 2 = 9 from by norm_num] at hm
    nlinarith [hm]
  have htriple : s13KerOn Q U1 ⊓ s13KerOn Q U2 ⊓ s13KerOn Q U3 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine w16n_all_ker_eq_bot h x (hH1.1 hx.1.1) ?_
    intro U hU
    rw [hSeq] at hU
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
    rcases hU with rfl | rfl | rfl
    · exact hx.1.1
    · exact hx.1.2
    · exact hx.2
  have hR1ne : s13KerOn Q U2 ⊓ s13KerOn Q U3 ≠ ⊥ := by
    intro hb
    rw [hb] at hR1card
    simp at hR1card
  have hR2ne : s13KerOn Q U1 ⊓ s13KerOn Q U3 ≠ ⊥ := by
    intro hb
    rw [hb] at hR2card
    simp at hR2card
  have hR3ne : s13KerOn Q U1 ⊓ s13KerOn Q U2 ≠ ⊥ := by
    intro hb
    rw [hb] at hR3card
    simp at hR3card
  have hR1not : ¬ (s13KerOn Q U2 ⊓ s13KerOn Q U3) ≤ s13KerOn Q U1 := by
    intro hle
    have hle' : s13KerOn Q U2 ⊓ s13KerOn Q U3 ≤
        s13KerOn Q U1 ⊓ s13KerOn Q U2 ⊓ s13KerOn Q U3 :=
      le_inf (le_inf hle inf_le_left) inf_le_right
    rw [htriple] at hle'
    exact hR1ne (le_bot_iff.mp hle')
  have hR2not : ¬ (s13KerOn Q U1 ⊓ s13KerOn Q U3) ≤ s13KerOn Q U2 := by
    intro hle
    have hle' : s13KerOn Q U1 ⊓ s13KerOn Q U3 ≤
        s13KerOn Q U1 ⊓ s13KerOn Q U2 ⊓ s13KerOn Q U3 :=
      le_inf (le_inf inf_le_left hle) inf_le_right
    rw [htriple] at hle'
    exact hR2ne (le_bot_iff.mp hle')
  have hR3not : ¬ (s13KerOn Q U1 ⊓ s13KerOn Q U2) ≤ s13KerOn Q U3 := by
    intro hle
    have hle' : s13KerOn Q U1 ⊓ s13KerOn Q U2 ≤
        s13KerOn Q U1 ⊓ s13KerOn Q U2 ⊓ s13KerOn Q U3 :=
      le_inf (le_inf inf_le_left inf_le_right) hle
    rw [htriple] at hle'
    exact hR3ne (le_bot_iff.mp hle')
  have hR12 : s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔ (s13KerOn Q U1 ⊓ s13KerOn Q U3)
      = s13KerOn Q U3 := by
    have hle : s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔ (s13KerOn Q U1 ⊓ s13KerOn Q U3)
        ≤ s13KerOn Q U3 := sup_le inf_le_right inf_le_right
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hdvd : Nat.card ↥(s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔
        (s13KerOn Q U1 ⊓ s13KerOn Q U3)) ∣ 9 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [hH3card] at this
    have hge : 3 ≤ Nat.card ↥(s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔
        (s13KerOn Q U1 ⊓ s13KerOn Q U3)) := by
      have hd := Subgroup.card_dvd_of_le
        (show s13KerOn Q U2 ⊓ s13KerOn Q U3 ≤
          s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔ (s13KerOn Q U1 ⊓ s13KerOn Q U3) from le_sup_left)
      rw [hR1card] at hd
      exact Nat.le_of_dvd Nat.card_pos hd
    have hne3 : Nat.card ↥(s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔
        (s13KerOn Q U1 ⊓ s13KerOn Q U3)) ≠ 3 := by
      intro h3
      have heq : s13KerOn Q U2 ⊓ s13KerOn Q U3 =
          s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔ (s13KerOn Q U1 ⊓ s13KerOn Q U3) :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hR1card])
      have hle' : s13KerOn Q U1 ⊓ s13KerOn Q U3 ≤ s13KerOn Q U2 ⊓ s13KerOn Q U3 := by
        rw [heq]; exact le_sup_right
      have heqR : s13KerOn Q U2 ⊓ s13KerOn Q U3 = s13KerOn Q U1 ⊓ s13KerOn Q U3 :=
        (Subgroup.eq_of_le_of_card_ge hle' (by rw [hR2card, hR1card])).symm
      exact hR1not (heqR ▸ inf_le_left)
    have hdvd' : Nat.card ↥(s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔
        (s13KerOn Q U1 ⊓ s13KerOn Q U3)) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 from by norm_num]; exact hdvd
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp3).1 hdvd'
    have hk_eq : k = 2 := by
      interval_cases k
      · rw [hk] at hge; norm_num at hge
      · exact absurd (show Nat.card ↥(s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔
          (s13KerOn Q U1 ⊓ s13KerOn Q U3)) = 3 by rw [hk]; norm_num) hne3
      · rfl
    rw [hk, hk_eq, hH3card]
    norm_num
  have hQeq : s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔ (s13KerOn Q U1 ⊓ s13KerOn Q U3) ⊔
      (s13KerOn Q U1 ⊓ s13KerOn Q U2) = Q := by
    rw [hR12]
    exact w16n_sup_eq_Q hcardQ hH3.1 (le_trans inf_le_left hH1.1) hH3card
      (le_of_eq hR3card.symm) hR3not
  have hsupp1 : s13Supp Q (s13KerOn Q U2 ⊓ s13KerOn Q U3) = {U1} :=
    w16n_supp_of_le_ker h hU1 (le_trans inf_le_left hH2.1) (by
      intro U' hU' hne'
      rw [hSeq] at hU'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU'
      rcases hU' with rfl | rfl | rfl
      · exact absurd rfl hne'
      · exact inf_le_left
      · exact inf_le_right) hR1not
  have hsupp2 : s13Supp Q (s13KerOn Q U1 ⊓ s13KerOn Q U3) = {U2} :=
    w16n_supp_of_le_ker h hU2 (le_trans inf_le_left hH1.1) (by
      intro U' hU' hne'
      rw [hSeq] at hU'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU'
      rcases hU' with rfl | rfl | rfl
      · exact inf_le_left
      · exact absurd rfl hne'
      · exact inf_le_right) hR2not
  have hsupp3 : s13Supp Q (s13KerOn Q U1 ⊓ s13KerOn Q U2) = {U3} :=
    w16n_supp_of_le_ker h hU3 (le_trans inf_le_left hH1.1) (by
      intro U' hU' hne'
      rw [hSeq] at hU'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU'
      rcases hU' with rfl | rfl | rfl
      · exact inf_le_left
      · exact inf_le_right
      · exact absurd rfl hne') hR3not
  have hrkR1 : rk ↥(commSub ⊤ (s13KerOn Q U2 ⊓ s13KerOn Q U3)) = 2 := by
    rw [w16n_rk_of_supp_singleton h hU1 (le_trans inf_le_left hH2.1) hsupp1, hrk U1 hU1]
  have hrkR2 : rk ↥(commSub ⊤ (s13KerOn Q U1 ⊓ s13KerOn Q U3)) = 2 := by
    rw [w16n_rk_of_supp_singleton h hU2 (le_trans inf_le_left hH1.1) hsupp2, hrk U2 hU2]
  have hrkR3 : rk ↥(commSub ⊤ (s13KerOn Q U1 ⊓ s13KerOn Q U2)) = 2 := by
    rw [w16n_rk_of_supp_singleton h hU3 (le_trans inf_le_left hH1.1) hsupp3, hrk U3 hU3]
  apply w16n_not_le_gen h
  have hR1gen : s13KerOn Q U2 ⊓ s13KerOn Q U3 ≤
      ⨆ (R : {R : Subgroup (MulAut W) // R ≤ Q ∧ rk ↥(commSub ⊤ R) = 2}),
        (R : Subgroup (MulAut W)) :=
    le_iSup (fun R : {R : Subgroup (MulAut W) // R ≤ Q ∧ rk ↥(commSub ⊤ R) = 2} =>
      (R : Subgroup (MulAut W))) ⟨_, le_trans inf_le_left hH2.1, hrkR1⟩
  have hR2gen : s13KerOn Q U1 ⊓ s13KerOn Q U3 ≤
      ⨆ (R : {R : Subgroup (MulAut W) // R ≤ Q ∧ rk ↥(commSub ⊤ R) = 2}),
        (R : Subgroup (MulAut W)) :=
    le_iSup (fun R : {R : Subgroup (MulAut W) // R ≤ Q ∧ rk ↥(commSub ⊤ R) = 2} =>
      (R : Subgroup (MulAut W))) ⟨_, le_trans inf_le_left hH1.1, hrkR2⟩
  have hR3gen : s13KerOn Q U1 ⊓ s13KerOn Q U2 ≤
      ⨆ (R : {R : Subgroup (MulAut W) // R ≤ Q ∧ rk ↥(commSub ⊤ R) = 2}),
        (R : Subgroup (MulAut W)) :=
    le_iSup (fun R : {R : Subgroup (MulAut W) // R ≤ Q ∧ rk ↥(commSub ⊤ R) = 2} =>
      (R : Subgroup (MulAut W))) ⟨_, le_trans inf_le_left hH1.1, hrkR3⟩
  calc Q = s13KerOn Q U2 ⊓ s13KerOn Q U3 ⊔ (s13KerOn Q U1 ⊓ s13KerOn Q U3) ⊔
        (s13KerOn Q U1 ⊓ s13KerOn Q U2) := hQeq.symm
    _ ≤ _ := sup_le (sup_le hR1gen hR2gen) hR3gen

private theorem w16n_rk_t (h : HNon A Q O t) (hS3 : (s13IsoComps Q).ncard = 3) :
    rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hrk : ∀ U ∈ s13IsoComps Q, rk ↥U = 2 := w16n_ranks_eq_two_of_ncard_three h hS3
  have ht2' : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := by
    intro x hx
    rw [h.hQinv x hx]
    exact Q.inv_mem hx
  have htQ' : ∀ x ∈ Q, t⁻¹ * x * t ∈ Q := by
    intro x hx
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2'
    simpa only [htinv] using htQ x hx
  have hsS : ∀ U ∈ s13IsoComps Q, U.map t.toMonoidHom ∈ s13IsoComps Q :=
    fun U hU => map_mem_s13IsoComps htQ htQ' hU
  have hfix : ∀ U ∈ s13IsoComps Q, U.map t.toMonoidHom = U →
      3 = 3 ∧ ∀ x ∈ Q, t * x * t⁻¹ * x ∈ s13KerOn Q U := by
    intro U hU _
    refine ⟨rfl, fun x hx => ?_⟩
    rw [h.hQinv x hx, inv_mul_cancel]
    exact (s13KerOn Q U).one_mem
  have hcost := s13_cost_eq h.hW (Or.inl rfl) h.hQe ht2' htQ (fun U hU => hU) hsS hfix
  have hsup : (⨆ U ∈ s13IsoComps Q, U) = commSub ⊤ Q := iSup_s13IsoComps h.hW (w16n_Q_odd h)
  rw [hsup] at hcost
  have hsum : (∑ᶠ (U : Subgroup W) (_ : U ∈ s13IsoComps Q), rk ↥U) = 6 := by
    classical
    haveI : Finite (Subgroup W) :=
      Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
    haveI : Fintype {U : Subgroup W // U ∈ s13IsoComps Q} := Fintype.ofFinite _
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
    have hcardN : Nat.card {U : Subgroup W // U ∈ s13IsoComps Q} = 3 := by
      rw [Nat.card_coe_set_eq, hS3]
    have hcong := Finset.sum_congr rfl
      (fun i (_ : i ∈ (Finset.univ : Finset {U : Subgroup W // U ∈ s13IsoComps Q})) =>
        hrk i.1 i.2)
    rw [hcong, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcardN,
      Nat.nsmul_eq_mul]
  rw [hsum] at hcost
  have h3 : rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) = 3 := by omega
  have hle : rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) := rk_mono (commSub_mono le_top le_rfl)
  have hle' : 3 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by rw [← h3]; exact hle
  exact le_antisymm h.hrk hle'

theorem w16n_shape_aux (h : HNon A Q O t) :
    Nat.card ↥Q = 9 ∧ (s13IsoComps Q).ncard = 3 ∧ (∀ U ∈ s13IsoComps Q, rk ↥U = 2) ∧
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 := by
  obtain ⟨d, hd⟩ := w16n_Q_card_pow h
  have hSnc_le : (s13IsoComps Q).ncard ≤ 3 := (w16n_components h).2.2
  have hSne : (s13IsoComps Q).Nonempty := w16n_comps_nonempty h
  have hdle : d ≤ (s13IsoComps Q).ncard := by
    have hle := w16n_card_le h
    rw [hd] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have hdne0 : d ≠ 0 := by
    intro hd0
    exact h.hQ1 (Subgroup.card_eq_one.mp (by rw [hd, hd0]; norm_num))
  have hdne1 : d ≠ 1 := by
    intro hd1
    exact w16n_card_ne_three h (by rw [hd, hd1]; norm_num)
  have hS1 : (s13IsoComps Q).ncard ≠ 1 := by
    intro h1
    omega
  have hS2 : (s13IsoComps Q).ncard ≠ 2 := w16n_ncard_ne_two h
  have hS3 : (s13IsoComps Q).ncard = 3 := by omega
  have hd2 : d = 2 := by
    rcases (by omega : d = 2 ∨ d = 3) with h2 | h3
    · exact h2
    · exfalso
      exact w16n_not_three_three h ⟨hS3, by rw [hd, h3]; norm_num⟩
  refine ⟨?_, hS3, w16n_ranks_eq_two_of_ncard_three h hS3, w16n_rk_t h hS3⟩
  rw [hd, hd2]
  norm_num

end CFSG.LocalAnalysis.WeakClosure81
