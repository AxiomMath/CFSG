module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Borel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_map_eq_sylow {X Y : Type} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Surjective f) {P : Subgroup X} (hP : IsSylowTwoOf P ⊤) {y : Y}
    (hy : y ∈ Subgroup.normalizer ((P.map f : Subgroup Y) : Set Y)) :
    ∃ b ∈ Subgroup.normalizer (P : Set X), ∃ s ∈ P.map f, f b = s * y := by
  obtain ⟨b₀, rfl⟩ := hf y
  set P' := P.map (MulAut.conj b₀).toMonoidHom with hP'
  have hPP : P ≤ P ⊔ f.ker := le_sup_left
  have hP'P : P' ≤ P ⊔ f.ker := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← Subgroup.comap_map_eq]
    show f (b₀ * p * b₀⁻¹) ∈ P.map f
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hy (f p)).mp ⟨p, hp, rfl⟩
  have hS1 : IsSylowTwoOf P (P ⊔ f.ker) := A4.isSylowTwoOf_mono hP hPP le_top
  have hP'syl : IsSylowTwoOf P' ⊤ := by
    refine ⟨le_top, hP.2.1.map _, ?_⟩
    have e1 : (P'.subgroupOf ⊤).index = P'.index := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    have e2 : (P.subgroupOf ⊤).index = P.index := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    rw [e1, hP', show (MulAut.conj b₀).toMonoidHom = ((MulAut.conj b₀ : X ≃* X) : X →* X)
      from rfl, Subgroup.index_map_equiv, ← e2]
    exact hP.2.2
  have hS2 : IsSylowTwoOf P' (P ⊔ f.ker) := A4.isSylowTwoOf_mono hP'syl hP'P le_top
  obtain ⟨c, hc, hcP⟩ := B6.isSylowTwoOf_exists_conj hS2 hS1
  refine ⟨c * b₀, ?_, f c, ?_, by rw [map_mul]⟩
  · apply mem_normalizer_of_map_conj_eq_ch625
    have e : P = (P'.map (MulAut.conj c).toMonoidHom) := hcP
    rw [map_conj_mul_ch625]
    exact e.symm
  · have : f c ∈ (P ⊔ f.ker).map f := ⟨c, hc, rfl⟩
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq] at this

namespace Hyp611Nat

variable {T M L V : Subgroup G} {n : ℕ}

theorem exists_two_pow_eq_one_of_mem_L_inf (h : Hyp611Nat G T M L V n) {x : G} (hxL : x ∈ L)
    (hxI : x ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) : ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
  obtain ⟨⟨v, hvZ⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.ZS_ne_bot
  have hv1' : v ≠ 1 := fun h0 => hv1 (Subtype.ext h0)
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨a, ?_⟩
  have hord : orderOf (x ^ (2 ^ a)) = b := by
    rw [orderOf_pow' x (pow_ne_zero a two_ne_zero), hab, Nat.gcd_mul_right_left]
    exact Nat.mul_div_cancel_left b (pow_pos two_pos a)
  have hc : x ^ (2 ^ a) * v = v * x ^ (2 ^ a) :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hxI _) v hvZ).symm
  exact h.eq_one_of_odd_of_commute (L.pow_mem hxL _) (hord ▸ hb) hvZ.1 hv1' hc

end Hyp611Nat

omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_subgroupOf_ch625 {K P : Subgroup G} (hPK : P ≤ K) {b : ↥K}
    (hb : b ∈ Subgroup.normalizer ((P.subgroupOf K : Subgroup ↥K) : Set ↥K)) :
    (b : G) ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  by_cases hz : z ∈ K
  · have h1 := Subgroup.mem_normalizer_iff.mp hb ⟨z, hz⟩
    simp only [Subgroup.mem_subgroupOf] at h1
    exact h1
  · constructor
    · intro hzP
      exact absurd (hPK hzP) hz
    · intro hzP
      exfalso
      apply hz
      have h2 : (b : G)⁻¹ * ((b : G) * z * (b : G)⁻¹) * (b : G) ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem b.2) (hPK hzP)) b.2
      simpa [mul_assoc] using h2

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

include hI in
theorem DL_le_normalizer_SK :
    DL ≤ Subgroup.normalizer ((ch6S T L V ⊓ K : Subgroup G) : Set G) := fun _ hx =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨d.hyp.DL_le_normalizer_S hI.h432 d.hall hx, d.DL_le_NK hI hx⟩

include hI in
theorem phi_DL_mul_inv_mem_SBar (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact) {x : G}
    (hx : x ∈ DL) {y : KBar K}
    (hy : y ∈ Subgroup.normalizer ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K))) :
    phiK K ⟨x, d.DL_le_NK hI hx⟩ y * y⁻¹ ∈ SBar T L V K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set dd := phiK K ⟨x, d.DL_le_NK hI hx⟩ with hdd
  have hdS : (SBar T L V K).map dd.toMonoidHom = SBar T L V K :=
    phi_mem_normalizer_SBar (d.DL_le_NK hI hx) (d.DL_le_normalizer_SK hI hx)
  have hdN : ∀ z ∈ Subgroup.normalizer ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K)),
      dd z ∈ Subgroup.normalizer ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K)) := by
    intro z hz
    apply mem_normalizer_of_map_conj_eq_ch625
    have e : (SBar T L V K).map (MulAut.conj (dd z)).toMonoidHom =
        (((SBar T L V K).map dd⁻¹.toMonoidHom).map (MulAut.conj z).toMonoidHom).map
          dd.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext w
      simp [MulAut.conj_apply]
    have hdS' : (SBar T L V K).map dd⁻¹.toMonoidHom = SBar T L V K := by
      conv_lhs => rw [← hdS]
      rw [Subgroup.map_map]
      have : (dd⁻¹.toMonoidHom.comp dd.toMonoidHom) = MonoidHom.id _ := by
        ext w
        simp
      rw [this, Subgroup.map_id]
    rw [e, hdS', map_conj_eq_of_mem_normalizer_ch6 hz, hdS]
  have hP := isSylowTwoOf_subgroupOf_top (d.isSylowTwoOf_SK hI.h432)
  obtain ⟨b, hbN, s, hs, hbs⟩ :=
    exists_mem_normalizer_map_eq_sylow (piK K) (piK_surjective K) hP hy
  have hbB : (b : G) ∈ K ⊓ Subgroup.normalizer ((ch6S T L V ⊓ K : Subgroup G) : Set G) :=
    ⟨b.2, mem_normalizer_of_mem_normalizer_subgroupOf_ch625 inf_le_right hbN⟩
  have hbM : (b : G) ∈ M := d.borel_le_M hI kf1 h23 hbB
  have hxL : x ∈ L := Hyp6116.DL_le_L d.hall hx
  have hxK := d.DL_le_NK hI hx
  have hcK : x * (b : G) * x⁻¹ * (b : G)⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hxK b).mp b.2) (K.inv_mem b.2)
  have hbL : (b : G) ∈ Subgroup.normalizer (L : Set G) := d.hyp.normal hbM
  have hcL : x * (b : G) * x⁻¹ * (b : G)⁻¹ ∈ L := by
    have e : x * (b : G) * x⁻¹ * (b : G)⁻¹ = x * ((b : G) * x⁻¹ * (b : G)⁻¹) := by group
    rw [e]
    exact L.mul_mem hxL ((Subgroup.mem_normalizer_iff.mp hbL _).mp (L.inv_mem hxL))
  obtain ⟨m, hm⟩ := d.hyp.toHyp611Nat.exists_two_pow_eq_one_of_mem_L_inf hcL (d.K_le_I hcK)
  have hpc : piK K ⟨_, hcK⟩ = dd (piK K b) * (piK K b)⁻¹ := by
    rw [hdd, phiK_piK, ← map_inv, ← map_mul]
    congr 1
  have hbNS :
      piK K b ∈ Subgroup.normalizer ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K)) := by
    rw [hbs]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hs) hy
  have hpcN : piK K ⟨_, hcK⟩ ∈
      Subgroup.normalizer ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K)) := by
    rw [hpc]
    exact Subgroup.mul_mem _ (hdN _ hbNS) (Subgroup.inv_mem _ hbNS)
  have hpc2 : ∃ m' : ℕ, (piK K ⟨_, hcK⟩) ^ (2 ^ m') = 1 := by
    refine ⟨m, ?_⟩
    rw [← map_pow]
    have e : (⟨_, hcK⟩ : ↥K) ^ (2 ^ m) = 1 := Subtype.ext (by simpa using hm)
    rw [e, map_one]
  have hpcS := mem_of_isSylowTwoOf_of_mem_normalizer (d.isSylowTwoOf_SBar hI.h432) hpc2 hpcN
  rw [hpc] at hpcS
  have hy' : y = s⁻¹ * piK K b := by rw [hbs]; group
  have hds : dd s ∈ SBar T L V K := by
    rw [← hdS]
    exact ⟨s, hs, rfl⟩
  rw [hy', map_mul, map_inv]
  rw [show (dd s)⁻¹ * dd (piK K b) * (s⁻¹ * piK K b)⁻¹ =
    (dd s)⁻¹ * (dd (piK K b) * (piK K b)⁻¹) * s by group]
  exact (SBar T L V K).mul_mem ((SBar T L V K).mul_mem ((SBar T L V K).inv_mem hds) hpcS) hs

omit d in
theorem mulAut_conj_conj {Q : Type*} [Group Q] (α : MulAut Q) (t : Q) :
    α * MulAut.conj t * α⁻¹ = MulAut.conj (α t) := by
  ext w
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

include hI in
theorem exists_SBar_moved (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact) {x : G}
    (hx : x ∈ DL) (hx1 : x ≠ 1) :
    ∃ s ∈ SBar T L V K, phiK K ⟨x, d.DL_le_NK hI hx⟩ s ≠ s := by
  by_contra hcon
  push Not at hcon
  set dd := phiK K ⟨x, d.DL_le_NK hI hx⟩ with hdd
  set D₀ := Subgroup.zpowers x with hD₀def
  have hD₀ : D₀ ≤ DL := Subgroup.zpowers_le.mpr hx
  have hD₀1 : D₀ ≠ ⊥ := fun h0 => hx1 (Subgroup.zpowers_eq_bot.mp h0)
  have hR24 := (d.hyp.lemma_6_1_24_two hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not).2.2 DL d.hall
    D₀ hD₀ hD₀1
  set Ker : Subgroup G := ((phiK K).ker).map (Subgroup.normalizer (K : Set G)).subtype with hKer
  have hmemKer : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (K : Set G)),
      phiK K ⟨y, hy⟩ = 1 → y ∈ Ker := fun y hy h => ⟨⟨y, hy⟩, h, rfl⟩
  have hxN := d.DL_le_NK hI hx
  have hfixj : ∀ (j : ℤ), ∀ s ∈ SBar T L V K, (dd ^ j) s = s := by
    intro j s hs
    have h1 : ∀ k : ℕ, (dd ^ k) s = s := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ, MulAut.mul_apply, hcon s hs, ih]
    rcases j with k | k
    · simpa using h1 k
    · rw [zpow_negSucc]
      nth_rewrite 1 [← h1 (k + 1)]
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hRK : ch6R T L V l ≤ Ker := by
    have hR' : ch6R T L V l = ⁅ch6R T L V l, D₀⁆ ⊔
        (ch6U T L V ⊓ Subgroup.centralizer (V : Set G)) := hR24
    rw [hR']
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro r hr y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hrN := d.R_le_NK hI hr
      have hjN : x ^ j ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpow_mem _ hxN j
      have hcN : ⁅r, x ^ j⁆ ∈ Subgroup.normalizer (K : Set G) := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hjN)
          (Subgroup.inv_mem _ hrN)) (Subgroup.inv_mem _ hjN)
      refine hmemKer _ hcN ?_
      have e : (⟨⁅r, x ^ j⁆, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⁅(⟨r, hrN⟩ : ↥(Subgroup.normalizer (K : Set G))), ⟨x, hxN⟩ ^ j⁆ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      obtain ⟨sr, hsr, hφr⟩ := d.exists_phi_R_eq_conj hI kf1 h23 hr
      have hcomm : dd ^ j * MulAut.conj sr = MulAut.conj sr * dd ^ j := by
        have h3 := mulAut_conj_conj (dd ^ j) sr
        rw [hfixj j sr hsr] at h3
        calc dd ^ j * MulAut.conj sr = (dd ^ j * MulAut.conj sr * (dd ^ j)⁻¹) * dd ^ j := by
              group
          _ = MulAut.conj sr * dd ^ j := by rw [h3]
      rw [e, map_commutatorElement, map_zpow, hφr, ← hdd, commutatorElement_def, ← hcomm]
      group
    · intro y hy
      have hyO : y ∈ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
        (d.hyp.lemma_6_1_20_one hI.h432).1 hy.1
      exact hmemKer _ _ (d.phi_eq_one_of_mem_pCoreOf hyO)
  obtain ⟨r, hr, hr1⟩ := d.exists_phi_R_ne_one hI
  obtain ⟨⟨y, hyN⟩, hy1, hyr⟩ := hRK hr
  have e : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨r, d.R_le_NK hI hr⟩ :=
    Subtype.ext hyr
  rw [e] at hy1
  exact hr1 hy1

include hI in
theorem kf2_cases (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact)
    (h23 : A23SQTKListFact) {x : G} (hx : x ∈ DL) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hxr : orderOf x = r) :
    IsLieChar2Big (KBar K) ∨
      (r = 7 ∧ phiK K ⟨x, d.DL_le_NK hI hx⟩ ∈ innAut (KBar K) ∧ Is3D4 2 1 (KBar K)) ∨
      (r = 3 ∧ phiK K ⟨x, d.DL_le_NK hI hx⟩ ∈ innAut (KBar K) ∧ IsSporadic .J2 (KBar K)) ∨
      (r = 3 ∧ phiK K ⟨x, d.DL_le_NK hI hx⟩ ∈ innAut (KBar K) ∧ ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 (KBar K)) := by
  obtain ⟨hs, hnab⟩ := isSimpleGroup_KBar d.quasi
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxr
    exact hr.one_lt.ne hxr
  have : Fact r.Prime := ⟨hr⟩
  have hord : orderOf (phiK K ⟨x, d.DL_le_NK hI hx⟩) = r := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have e : (⟨x, d.DL_le_NK hI hx⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ r = 1 :=
        Subtype.ext (by simp [← hxr, pow_orderOf_eq_one])
      rw [e, map_one]
    · intro h0
      exact hx1 (d.eq_one_of_phi_DL hI hx h0)
  exact kf2 (KBar K) hs hnab (d.a23List_KBar h23) (SBar T L V K) (d.isSylowTwoOf_SBar hI.h432) _ r
    hr hr2 hord (phi_mem_normalizer_SBar (d.DL_le_NK hI hx) (d.DL_le_normalizer_SK hI hx))
    (d.exists_SBar_moved hI kf1 h23 hx hx1)
    (fun y hy => d.phi_DL_mul_inv_mem_SBar hI kf1 h23 hx hy)

end Dat625

end CFSG.Quasithin.H13
