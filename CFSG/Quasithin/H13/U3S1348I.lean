module

public import CFSG.Quasithin.H13.U3S1348H
public import CFSG.Quasithin.H13.U3S1348C
public import CFSG.Quasithin.H13.U3S13227
public import CFSG.Quasithin.H13.U3S1344
public import CFSG.Quasithin.H13.U3S1348E

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

section Blocks

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} {hV : IsElemAbelian 2 V}

theorem blocks_conjAut_eq_of_pow_three {H R : Subgroup G}
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod V hV)))} (B : BlocksR (hV := hV) H R 𝓗 𝓘)
    (hcard : 𝓘.card ≤ 2) {d : MulAut (IntMod V hV)} (hd : d ∈ autI hV H) (hd3 : d ^ 3 = 1)
    {K : Subgroup (MulAut (IntMod V hV))} (hK : K ∈ 𝓘) : B1.conjAut d K = K := by
  have hinj : ∀ A A' : Subgroup (MulAut (IntMod V hV)), B1.conjAut d A = B1.conjAut d A' →
      A = A' := fun A A' h =>
    le_antisymm ((B1.conjAut_le_iff (g := d)).1 h.le) ((B1.conjAut_le_iff (g := d)).1 h.ge)
  have hmul : ∀ A : Subgroup (MulAut (IntMod V hV)),
      B1.conjAut (d ^ 3) A = B1.conjAut d (B1.conjAut d (B1.conjAut d A)) := by
    intro A
    ext x
    simp only [B1.mem_conjAut, pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  have hone : ∀ A : Subgroup (MulAut (IntMod V hV)), B1.conjAut 1 A = A := fun A => by
    ext x
    simp [B1.mem_conjAut]
  rcases BlocksR.eq_pair_of_card_le_two hK hcard with hI | ⟨K', hK', hne, hall⟩
  · have h1 := B.conjAut_mem hd hK
    rw [hI, Finset.mem_singleton] at h1
    exact h1
  · by_contra hK1
    have h1 : B1.conjAut d K = K' := (hall _ (B.conjAut_mem hd hK)).resolve_left hK1
    have h2 : B1.conjAut d K' = K := by
      rcases hall _ (B.conjAut_mem hd hK') with h | h
      · exact h
      · exact absurd (hinj K K' (h1.trans h.symm)) (Ne.symm hne)
    have h3 := hmul K
    rw [hd3, hone, h1, h2, h1] at h3
    exact hne h3.symm

theorem blocks_comm_of_pow_three {H R : Subgroup G}
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod V hV)))} (B : BlocksR (hV := hV) H R 𝓗 𝓘)
    (hcard : 𝓘.card ≤ 2) {d : MulAut (IntMod V hV)} (hd : d ∈ autI hV H) (hd3 : d ^ 3 = 1)
    {K : Subgroup (MulAut (IntMod V hV))} (hK : K ∈ 𝓘) {c : MulAut (IntMod V hV)} (hc : c ∈ K)
    (hc3 : orderOf c = 3) : d * c = c * d := by
  have hfix := blocks_conjAut_eq_of_pow_three B hcard hd hd3 hK
  have hdK : ∀ y ∈ K, d * y * d⁻¹ ∈ K := by
    intro y hy
    rw [← hfix, B1.mem_conjAut]
    simpa [mul_assoc] using hy
  have h := conj_eq_self_of_pow_three (B.hb.card_eq K (B.sub hK)) hc hc3 hdK hd3
  calc d * c = (d * c * d⁻¹) * d := by group
    _ = c * d := by rw [h]

end Blocks

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_odd_trivial (S : A6.Setting134 G T L V) {Lp : Subgroup G} (P : S134Plus S Lp)
    {z : G} {H VH : Subgroup G} (hHz : InHz T L V z H) (hsolv : Group.IsSolvable ↥H)
    (hred : IsTwoReducedIn H VH) (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G))
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))}
    (B : BlocksR (hV := hred.2.2.1) H (r1Of T L V) 𝓗 𝓘) (hcard : 𝓘.card ≤ 2) {d : G}
    (hdL : d ∈ Lp) (hdN : d ∈ normalizer (VH : Set G))
    (hdI : convI hred.2.2.1 ⟨d, hdN⟩ ∈ ⨆ K ∈ 𝓘, K) (hodd : ∃ m, Odd m ∧ d ^ m = 1) :
    d ∈ centralizer (VH : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTsyl, hL1TH, -, -, -⟩ := s134_inHz_facts S hHz
  have hRH : r1Of T L V ≤ H := (r1Of_le_T T L V).trans hTsyl.1
  have hVR : VH ≤ r1Of T L V :=
    (s134_VH_le_r1Of hred hcR).1.trans (s134_VH_le_r1Of hred hcR).2
  have hR2 : IsPGroup 2 ↥(r1Of T L V) := S.h13.sylow.1.to_le (r1Of_le_T T L V)
  have hRN : r1Of T L V ≤ normalizer (VH : Set G) := hRH.trans hred.2.1
  have hTR : T ≤ normalizer (r1Of T L V : Set G) := by
    rw [← P.pCoreOf_eq_r1Of]
    exact le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hmeet : ∀ K ∈ 𝓘, autI hred.2.2.1 (thompsonJ (r1Of T L V)) ⊓ K ≠ ⊥ := fun K hK =>
    B.inf_ne_bot hred hsolv hVR hRH hJ hTsyl hTR hcard hK
  have hdR : d ∈ normalizer (r1Of T L V : Set G) := by
    rw [← P.pCoreOf_eq_r1Of]
    exact le_normalizer_pCoreOf 2 _ (mem_sup_left hdL)
  have hdJ : d ∈ normalizer (thompsonJ (r1Of T L V) : Set G) :=
    CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _ hdR
  have hconj : ∀ g : G, (hg : g ∈ normalizer (VH : Set G)) →
      g ∈ normalizer (thompsonJ (r1Of T L V) : Set G) →
      B1.conjAut (convI hred.2.2.1 ⟨g, hg⟩) (autI hred.2.2.1 (thompsonJ (r1Of T L V))) =
        autI hred.2.2.1 (thompsonJ (r1Of T L V)) := fun g hg hgJ => by
    rw [conjAut_eq_map, autI_cjSub hred.2.2.1 hg, B2F.cjSub_eq_of_mem_normalizer hgJ]
  have hN : convI hred.2.2.1 ⟨d, hdN⟩ ∈ normalizer
      ((autI hred.2.2.1 (thompsonJ (r1Of T L V)) : Subgroup (MulAut (IntMod VH hred.2.2.1))) :
        Set (MulAut (IntMod VH hred.2.2.1))) := by
    refine E2.mem_normalizer_of_conjAut_le (hconj d hdN hdJ).le ?_
    have h1 := hconj d⁻¹ (inv_mem hdN) (inv_mem hdJ)
    rw [show (⟨d⁻¹, inv_mem hdN⟩ : ↥(normalizer (VH : Set G))) = (⟨d, hdN⟩)⁻¹ from rfl,
      map_inv] at h1
    exact h1.le
  have hodd' : ∃ m, Odd m ∧ (convI hred.2.2.1 ⟨d, hdN⟩) ^ m = 1 := by
    obtain ⟨m, hm, hdm⟩ := hodd
    refine ⟨m, hm, ?_⟩
    rw [← map_pow]
    have : (⟨d, hdN⟩ : ↥(normalizer (VH : Set G))) ^ m = 1 := Subtype.ext (by simpa using hdm)
    rw [this, map_one]
  have h1 := B.eq_one_of_normalizes hcard hR2 (hRN) hmeet hdI hodd' hN
  exact (convI_eq_one_iff hred.2.2.1 _).1 h1

theorem exists_three_elt_I {VH : Subgroup G} {hV : IsElemAbelian 2 VH} {H R : Subgroup G}
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hV)))} (B : BlocksR (hV := hV) H R 𝓗 𝓘)
    (hne : 𝓘.Nonempty) :
    ∃ x ∈ conjClosure (thompsonJ R) H, (∃ k : ℕ, x ^ 3 ^ k = 1) ∧
      ∃ hx : x ∈ normalizer (VH : Set G), convI hV ⟨x, hx⟩ ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := hne
  obtain ⟨c, hcK, hc3⟩ := exists_orderOf_three_of_card_six (B.hb.card_eq K (B.sub hK))
  have hcI : c ∈ autI hV (conjClosure (thompsonJ R) H) := by
    rw [B.eq]
    exact le_iSup₂_of_le (f := fun (K' : Subgroup (MulAut (IntMod VH hV))) (_ : K' ∈ 𝓘) => K')
      K hK le_rfl hcK
  obtain ⟨y, hyI, hyc⟩ := (mem_autI hV).1 hcI
  obtain ⟨b, m, hm3, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (y : G)).ne' 3
    (by norm_num)
  refine ⟨(y : G) ^ m, pow_mem hyI m, ⟨b, ?_⟩, pow_mem y.2 m, ?_⟩
  · rw [← pow_mul, mul_comm, ← hbm, pow_orderOf_eq_one]
  · have h1 : (⟨(y : G) ^ m, pow_mem y.2 m⟩ : ↥(normalizer (VH : Set G))) = y ^ m :=
      Subtype.ext (by simp)
    rw [h1, map_pow, hyc]
    intro h
    exact hm3 (hc3 ▸ orderOf_dvd_of_pow_eq_one h)

theorem s134_mem_L1_of_three (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hxz : x ∈ centralizer ({z} : Set G))
    (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) : x ∈ L₁Of L (fsuV1 T V) := by
  have hyp := hyp1223_of h1332 S.h13 S.irr
  have hxL : x ∈ L := by
    rcases h1228 G T L V hyp with h | h | ⟨⟨n, -, -, hz3, -⟩, -⟩
    · rw [← h]
      exact subset_closure ⟨hxM, hx3⟩
    · exfalso
      obtain ⟨e⟩ := he
      rcases h with he5 | hl
      · obtain ⟨e5⟩ := he5
        have h1 := Nat.card_congr (e.symm.trans e5).toEquiv
        rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_fin,
          Nat.card_fin] at h1
        revert h1
        decide
      · exact s134_not_L32 S hl
    · exfalso
      obtain ⟨e6⟩ := he
      have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by simp)
      have hsQ : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := (MulEquiv.isSimpleGroup_congr e6).2 hs
      have hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := alt6_nonabelian
        exact ⟨e6.symm a, e6.symm b, fun h => hab (by simpa using congrArg e6 h)⟩
      rcases (inferInstance : (center (↥L ⧸ CFSG.pCore 2 ↥L)).Normal).eq_bot_or_eq_top with
        h | h
      · rw [h, Subgroup.card_bot] at hz3
        omega
      · obtain ⟨a, b, hab⟩ := hna
        exact hab (mem_center_iff.1 (h ▸ mem_top b) a)
  have hxzV : x * S.zV = S.zV * x :=
    mem_centralizer_iff.1 (S.mem_ZV_iff.2 (Or.inr rfl)).2 x hxL
  have hxz' : x * z = z * x := mem_centralizer_singleton_iff.1 hxz
  obtain ⟨hzV, hψz⟩ := s134_psi_z S hz hzL
  have hxV1 : x ∈ centralizer (fsuV1 T V : Set G) := by
    refine mem_centralizer_iff.2 fun w hw => ?_
    obtain ⟨hwV, hwW⟩ := S.mem_V1_iff.1 hw
    have hcases := W1_cases _ (S.frame.ψ ⟨w, hwV⟩).2 hwW
    have hw' : w = 1 ∨ w = S.zV ∨ w = z ∨ w = z * S.zV := by
      have hψ1 : (S.frame.ψ ⟨S.zV, S.zV_mem_V⟩ : P6) = G6.allOnes 6 := by rw [S.psi_zV]
      have key : ∀ a b : G, ∀ (ha : a ∈ V) (hb : b ∈ V),
          (S.frame.ψ ⟨a, ha⟩ : P6) = S.frame.ψ ⟨b, hb⟩ → a = b := fun a b ha hb h =>
        congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
      have hmul : (S.frame.ψ ⟨z * S.zV, mul_mem hzV S.zV_mem_V⟩ : P6) =
          (S.frame.ψ ⟨z, hzV⟩ : P6) * G6.allOnes 6 := by
        rw [show (⟨z * S.zV, mul_mem hzV S.zV_mem_V⟩ : ↥V) = ⟨z, hzV⟩ * ⟨S.zV, S.zV_mem_V⟩
          from rfl, map_mul, Subgroup.coe_mul, hψ1]
      rcases hcases with h | h | h | h
      · left
        have h1 : S.frame.ψ ⟨w, hwV⟩ = 1 := Subtype.ext h
        exact congrArg Subtype.val ((MulEquiv.map_eq_one_iff _).1 h1)
      · exact Or.inr (Or.inl (key _ _ hwV S.zV_mem_V (h.trans hψ1.symm)))
      · rcases hψz with hz' | hz'
        · exact Or.inr (Or.inr (Or.inl (key _ _ hwV hzV (h.trans hz'.symm))))
        · refine Or.inr (Or.inr (Or.inr (key _ _ hwV (mul_mem hzV S.zV_mem_V) ?_)))
          rw [hmul, hz', h, allOnes_eq_mul]
          decide
      · rcases hψz with hz' | hz'
        · refine Or.inr (Or.inr (Or.inr (key _ _ hwV (mul_mem hzV S.zV_mem_V) ?_)))
          rw [hmul, hz', h, allOnes_eq_mul]
          decide
        · exact Or.inr (Or.inr (Or.inl (key _ _ hwV hzV (h.trans hz'.symm))))
    rcases hw' with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hxzV.symm
    · exact hxz'.symm
    · calc z * S.zV * x = z * (S.zV * x) := by group
        _ = z * (x * S.zV) := by rw [hxzV]
        _ = (z * x) * S.zV := by group
        _ = (x * z) * S.zV := by rw [hxz']
        _ = x * (z * S.zV) := by group
  obtain ⟨k, hk⟩ := hx3
  exact mem_oTwoRes_of_odd (mem_inf.2 ⟨hxL, centralizer_le_normalizer _ hxV1⟩)
    (Odd.pow (by decide)) hk

theorem s134_I_not_le_M (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) {H VH : Subgroup G}
    (hHz : InHz T L V z H) (hsolv : Group.IsSolvable ↥H) (hred : IsTwoReducedIn H VH)
    (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G))
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))}
    (B : BlocksR (hV := hred.2.2.1) H (r1Of T L V) 𝓗 𝓘) (hne : 𝓘.Nonempty) (hcard : 𝓘.card ≤ 2) :
    ¬ conjClosure (thompsonJ (r1Of T L V)) H ≤ normalizer (L : Set G) := by
  intro hIM
  obtain ⟨-, -, hHzC, -, -⟩ := s134_inHz_facts S hHz
  have hIH : conjClosure (thompsonJ (r1Of T L V)) H ≤ H := conjClosure_le fun h hh j hj =>
    mul_mem (mul_mem hh ((((iSup₂_le fun _ hA => hA.1 :
      thompsonJ (r1Of T L V) ≤ r1Of T L V).trans (r1Of_le_T T L V)).trans
        (s134_inHz_facts S hHz).1.1) hj)) (inv_mem hh)
  obtain ⟨x, hxI, hx3, hxN, hx1⟩ := exists_three_elt_I B hne
  have hxL1 := s134_mem_L1_of_three h1332 h1228 S he hz hzL (hIM hxI) (hHzC (hIH hxI)) hx3
  have hxI' : convI hred.2.2.1 ⟨x, hxN⟩ ∈ ⨆ K ∈ 𝓘, K := by
    rw [← B.eq]
    exact convI_mem_autI _ hxI hxN
  obtain ⟨k, hk⟩ := hx3
  have hC := s134_odd_trivial S (s134Plus_L1 S he) hHz hsolv hred hcR hJ B hcard hxL1 hxN hxI'
    ⟨3 ^ k, Odd.pow (by decide), hk⟩
  exact hx1 ((convI_eq_one_iff _ _).2 hC)

end CFSG.Quasithin.H13.U3
