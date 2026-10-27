module

public import CFSG.Quasithin.Vol2.Ch12Sec7Orb
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_of_1222 (h1222 : Stmt12_2_2) {T L V : Subgroup G}
    (h : Hyp1271 G T L V) : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L := by
  have hy := h.hyp
  obtain ⟨-, -, hall⟩ := ((h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow).resolve_left
    hy.notAlt) L hy.maximal hy.faithful hy.quasisimple
  obtain ⟨-, -, -, ⟨_, hmod⟩⟩ := hall V hy.irrPlus
  have hQ := card_quot_of_hatA6Quot h.hatA6
  have hsl : ∀ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) →
      ¬ 135 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    intro n hn
    rcases hn with rfl | rfl | rfl <;> rw [Matrix.card_SL_field, ZMod.card] <;> decide
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨m, hm5, hm8, ⟨φ, hφ, hker⟩, -⟩ | ⟨-, φ, hφ, hker⟩ | ⟨hU, -⟩ | ⟨-, -, -, hCO, -, -⟩
  · exact absurd (dvd_card_quot_pCore h.hatA6 e) (hsl n hn)
  · exact absurd (dvd_card_quot_pCore h.hatA6 e) (hsl 3 (Or.inl rfl))
  · exact absurd (dvd_card_quot_pCore h.hatA6 e) (hsl 5 (Or.inr (Or.inr rfl)))
  · exfalso
    apply card_alternating_ne hm5 hm8
    rw [← hQ, ← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
  · exfalso
    apply card_alternating_ne (n := 7) (by norm_num) (by norm_num)
    rw [← hQ, ← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
  · exfalso
    rcases hU with ⟨-, hU⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have h135 := dvd_card_quot_pCore h.hatA6 (MulEquiv.refl _)
      rw [F420.card_of_u33 hU] at h135
      exact absurd h135 (by decide)
    all_goals exact absurd h0 (by norm_num)
  · exact hCO

omit [Finite G] in
theorem mem_fixV_zpowers {W : Type*} [CommGroup W] {c : MulAut W} {w : W} :
    w ∈ fixV (Subgroup.zpowers c) ↔ c w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

omit [Finite G] in
theorem exists_pow_mem_of_mem_sup {K P : Subgroup G} (hP : IsPGroup 2 P)
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ K ⊔ P) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ K := by
  obtain ⟨a, ha, p, hp, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hPK).1 hx
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq ha (hPK hp) (2 ^ k)
  exact ⟨k, by rw [hxe, hk', mul_one]; exact hx'⟩

omit [Finite G] in
theorem mem_normalizer_inf_centralizer {M V : Subgroup G} {g : G} (hgM : g ∈ M)
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ h ∈ M, h ∈ Subgroup.normalizer (V : Set G) →
      ∀ c ∈ M ⊓ Subgroup.centralizer (V : Set G),
        h * c * h⁻¹ ∈ M ⊓ Subgroup.centralizer (V : Set G) := by
    intro h hhM hhV c hc
    refine ⟨M.mul_mem (M.mul_mem hhM hc.1) (M.inv_mem hhM), Subgroup.mem_centralizer_iff.2
      fun v hv => ?_⟩
    have hv' : h⁻¹ * v * h ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hhV) v).1 hv
      rwa [inv_inv] at this
    have hcv := Subgroup.mem_centralizer_iff.1 hc.2 _ hv'
    calc v * (h * c * h⁻¹) = h * ((h⁻¹ * v * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * v * h)) * h⁻¹ := by rw [hcv]
      _ = h * c * h⁻¹ * v := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hgM hgV c, fun hc => ?_⟩
  have := key g⁻¹ (M.inv_mem hgM) (Subgroup.inv_mem _ hgV) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this

theorem mem_autOn_of_central {T K V : Subgroup G} (hT : quasithinIsSylowTwo T) (hTK : T ≤ K)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) {i : MulAut ↥V} (hi : i ∈ autOn K V)
    (hc : ∀ a ∈ autOn K V, a * i = i * a) (hi2 : i ^ 2 = 1) : i ∈ autOn T V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hTK.trans hKV
  obtain ⟨k, rfl⟩ := (A4.mem_autOn_iff hKV).1 hi
  obtain ⟨a, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  set k₂ := k ^ m with hk₂def
  have hk₂2 : k₂ ^ 2 ^ a = 1 := by
    rw [hk₂def, ← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hact : A4.actionOn V K hKV k₂ = A4.actionOn V K hKV k := by
    rw [hk₂def, map_pow]
    obtain ⟨j, rfl⟩ := hm
    rw [pow_succ, pow_mul, hi2, one_pow, one_mul]
  have hT2 : IsPGroup 2 (T.subgroupOf K) := hT.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  have hTidx : ¬ 2 ∣ (T.subgroupOf K).index := fun h2 =>
    hT.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))
  set S := hT2.toSylow hTidx with hSdef
  have hk2p : IsPGroup 2 (Subgroup.zpowers k₂) := by
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk₂2)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hb])
  obtain ⟨Q, hQ⟩ := hk2p.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥K S Q
  have hk₂Q : k₂ ∈ (Q : Subgroup ↥K) := hQ (Subgroup.mem_zpowers k₂)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hk₂Q
  obtain ⟨s, hs, hsk⟩ := hk₂Q
  rw [MulAut.smul_def, MulAut.conj_apply] at hsk
  have hsT : ((s : ↥K) : G) ∈ T := hs
  have hxa : A4.actionOn V K hKV x ∈ autOn K V := (A4.mem_autOn_iff hKV).2 ⟨x, rfl⟩
  have hcx := hc _ hxa
  have e1 : A4.actionOn V K hKV k = A4.actionOn V K hKV x * A4.actionOn V K hKV s *
      (A4.actionOn V K hKV x)⁻¹ := by
    rw [← hact, ← hsk, map_mul, map_mul, map_inv]
  have hcs : A4.actionOn V K hKV s = A4.actionOn V K hKV k := by
    calc A4.actionOn V K hKV s = (A4.actionOn V K hKV x)⁻¹ * A4.actionOn V K hKV k *
          A4.actionOn V K hKV x := by rw [e1]; group
      _ = A4.actionOn V K hKV k := by
          rw [mul_assoc, ← hcx, ← mul_assoc, inv_mul_cancel, one_mul]
  refine (A4.mem_autOn_iff hTV).2 ⟨⟨s, hsT⟩, ?_⟩
  rw [← hcs]
  ext v
  rfl

end S127

open S127 in
theorem lemma12_7_24_of (h1222 : Stmt12_2_2) (h2 : Lemma12_7_2) (h10 : Lemma12_7_10)
    (h23 : Lemma12_7_23) : Lemma12_7_24 := by
  intro G _ _ T L V t z hS
  classical
  obtain ⟨hcomm, hV64, hTV⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  have hCL := inf_centralizer_eq_of_1222 h1222 hS.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hS.hyp.hyp.irrPlus.2.2.1
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := hS.hyp.hyp.normalizes
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hLM : L ≤ M := Subgroup.le_normalizer
  obtain ⟨-, -, -, -, -, ⟨-, hset, -, -⟩, -⟩ := h2 G T L V hS.hyp
  have hL1 : L1 T L V ∈ {I : Subgroup G | I ≤ P1 T L V ∧ T ≤ Subgroup.normalizer (I : Set G) ∧
      oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} := by
    rw [hset]
    exact Set.mem_insert _ _
  obtain ⟨-, -, hL1O, hL13⟩ := hL1
  have hL1L : L1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hL2L : L2 T L V ≤ L := fun x hx => ((oTwoUpper_le _) hx).1
  obtain ⟨-, ⟨hr2, -⟩, hc, hd, he⟩ := h10 G T L V t hS.toSetting1273
  by_contra hr
  obtain ⟨U, hUV, hUN, hU3⟩ : ∃ U : Subgroup G, U ≤ V ∧
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      E3.mQuot V U ≤ 3 := by
    by_contra hne
    apply hr
    have h4 : (4 : ℕ∞) ≤ E3.rParam V := by
      refine le_iInf₂ fun U hU => ?_
      have : ¬ E3.mQuot V U ≤ 3 := fun h => hne ⟨U, hU.1, hU.2, h⟩
      exact_mod_cast (by omega : 4 ≤ E3.mQuot V U)
    exact lt_of_lt_of_le (by norm_num) h4
  have hU3' : E3.mQuot V U = 3 := by
    have h1 : E3.rParam V ≤ E3.mQuot V U := iInf₂_le U ⟨hUV, hUN⟩
    have h2' : (2 : ℕ∞) < (E3.mQuot V U : ℕ∞) := lt_of_lt_of_le hr2 h1
    have : 2 < E3.mQuot V U := by exact_mod_cast h2'
    omega
  have hR2 : R2 T L V ≤ M ⊓ Subgroup.normalizer (V : Set G) := by
    intro r hr'
    have hr1 : r ∈ L ⊔ pCoreOf 2 (L ⊔ T) := ((pCoreOf_le 2 _) hr').1
    have hLT : L ⊔ pCoreOf 2 (L ⊔ T) ≤ M ⊓ Subgroup.normalizer (V : Set G) :=
      sup_le (le_inf hLM hLV) ((pCoreOf_le 2 _).trans (sup_le (le_inf hLM hLV) (le_inf hTM hTV)))
    exact hLT hr1
  have hUM : ¬ Subgroup.centralizer (U : Set G) ≤ M := by
    intro hle
    apply hUN
    intro x hx
    have hxM : x ∈ M ⊓ Subgroup.centralizer (U : Set G) := ⟨hle hx, hx⟩
    rcases hd U hUV hU3' with hi | ⟨l, hl, -, -, hii⟩ | ⟨-, -, -, -, -, i, hi, -, hiii⟩
    · rw [hi] at hxM
      exact Subgroup.centralizer_le_normalizer _ hxM.2
    · have hlx : l * x * l⁻¹ ∈ M ⊓ Subgroup.centralizer
          ((U.map (MulAut.conj l).toMonoidHom : Subgroup G) : Set G) := by
        refine ⟨M.mul_mem (M.mul_mem (hLM hl) hxM.1) (M.inv_mem (hLM hl)),
          Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
        obtain ⟨u', hu', rfl⟩ := hu
        have hc' := Subgroup.mem_centralizer_iff.1 hx u' hu'
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc l * u' * l⁻¹ * (l * x * l⁻¹) = l * (u' * x) * l⁻¹ := by group
          _ = l * (x * u') * l⁻¹ := by rw [hc']
          _ = l * x * l⁻¹ * (l * u' * l⁻¹) := by group
      rw [hii] at hlx
      have hsub : (M ⊓ Subgroup.centralizer (V : Set G)) ⊔ R2 T L V ≤
          Subgroup.normalizer (V : Set G) :=
        sup_le (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
          (hR2.trans inf_le_right)
      have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLV hl)) (hsub hlx))
        (hLV hl)
      rwa [show l⁻¹ * (l * x * l⁻¹) * l = x by group] at h1
    · rw [hiii] at hxM
      have hsub : Subgroup.zpowers i ⊔ (M ⊓ Subgroup.centralizer (V : Set G)) ≤
          Subgroup.normalizer (V : Set G) :=
        sup_le ((Subgroup.zpowers_le).2 hi.2)
          (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
      exact hsub hxM
  obtain ⟨y, hyM, hyL, hy2, -, hUy⟩ := he U hUV hU3' hUM
  have hlt : autOn L V < hS.hyp.hyp.MVbar := by
    refine lt_of_le_of_ne (A4.autOn_mono (le_inf hLM hLV)) fun h => hyL ?_
    rw [h]
    exact hyM
  obtain ⟨i₁, -, i₂, -, -, -, hi₁2, hi₂2, hcls, -, hZ1, hZ2, hc1, hc2, -, -⟩ := hc hlt
  obtain ⟨i, K, hTK, hKV, hZ, hci, hi2, m, hm, hym⟩ : ∃ (i : MulAut ↥V) (K : Subgroup G),
      T ≤ K ∧ K ≤ Subgroup.normalizer (V : Set G) ∧
      autOn K V ⊓ Subgroup.centralizer (autOn K V : Set (MulAut ↥V)) = Subgroup.zpowers i ∧
      Nat.card ↥(fixV (Subgroup.zpowers i)) = 8 ∧ orderOf i = 2 ∧
      ∃ m ∈ hS.hyp.hyp.MVbar, y = m * i * m⁻¹ := by
    rcases hcls y hyM hyL hy2 with ⟨m, hm, hym⟩ | ⟨m, hm, hym⟩
    · exact ⟨i₁, L1 T L V ⊔ T, le_sup_right, sup_le (hL1L.trans hLV) hTV, hZ1, hc1, hi₁2, m,
        hm, hym⟩
    · exact ⟨i₂, L2 T L V ⊔ T, le_sup_right, sup_le (hL2L.trans hLV) hTV, hZ2, hc2, hi₂2, m,
        hm, hym⟩
  have hiK : i ∈ autOn K V ⊓ Subgroup.centralizer (autOn K V : Set (MulAut ↥V)) :=
    hZ ▸ Subgroup.mem_zpowers i
  have hisq : i ^ 2 = 1 := by rw [← hi2, pow_orderOf_eq_one]
  have hiT : i ∈ autOn T V := mem_autOn_of_central hS.hyp.hyp.sylow hTK hKV hiK.1
    (fun a ha => Subgroup.mem_centralizer_iff.1 hiK.2 a ha) hisq
  set Uj := (fixV (Subgroup.zpowers i)).map V.subtype with hUjdef
  have hUjV : Uj ≤ V := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hmemUj : ∀ w : ↥V, (w : G) ∈ Uj ↔ i w = w := by
    intro w
    constructor
    · rintro ⟨w', hw', hww'⟩
      rw [show w' = w from Subtype.ext hww'] at hw'
      exact mem_fixV_zpowers.1 hw'
    · intro h
      exact ⟨w, mem_fixV_zpowers.2 h, rfl⟩
  have hzV : z ∈ V := (Subgroup.mem_inf.1 hS.z_mem).1
  have hzUj : z ∈ Uj := by
    obtain ⟨s, hs⟩ := (A4.mem_autOn_iff hTV).1 hiT
    refine (hmemUj ⟨z, hzV⟩).2 (Subtype.ext ?_)
    rw [← hs, A4.actionOn_apply_coe]
    have := Subgroup.mem_centralizer_singleton_iff.1 (hS.T_le_Gz s.2)
    show (s : G) * z * (s : G)⁻¹ = z
    rw [this, mul_inv_cancel_right]
  have hTUj : T ≤ Subgroup.normalizer (Uj : Set G) := by
    have key : ∀ s ∈ T, ∀ u ∈ Uj, s * u * s⁻¹ ∈ Uj := by
      intro s hs u hu
      obtain ⟨w, hw, rfl⟩ := hu
      have hw' : i w = w := mem_fixV_zpowers.1 hw
      set a := A4.actionOn V T hTV ⟨s, hs⟩ with ha
      have haK : a ∈ autOn K V := A4.autOn_mono hTK ((A4.mem_autOn_iff hTV).2 ⟨⟨s, hs⟩, rfl⟩)
      have hai : a * i = i * a := Subgroup.mem_centralizer_iff.1 hiK.2 a haK
      have h1 : ((a w : ↥V) : G) = s * w * s⁻¹ := A4.actionOn_apply_coe hTV _ w
      show s * (w : G) * s⁻¹ ∈ Uj
      rw [← h1]
      refine (hmemUj (a w)).2 ?_
      have h2 := congrArg (fun f : MulAut ↥V => f w) hai
      simp only [MulAut.mul_apply] at h2
      rw [← h2, hw']
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨key s hs u, fun hu => ?_⟩
    have := key s⁻¹ (T.inv_mem hs) _ hu
    rwa [show s⁻¹ * (s * u * s⁻¹) * s⁻¹⁻¹ = u by group] at this
  have hUjM : ¬ Subgroup.centralizer (Uj : Set G) ≤ M := by
    intro hle
    apply hUM
    obtain ⟨g, hg⟩ := (A4.mem_autOn_iff inf_le_right).1 hm
    have hgU : ∀ u ∈ Uj, (g : G) * u * (g : G)⁻¹ ∈ U := by
      intro u hu
      obtain ⟨w, hw, rfl⟩ := hu
      have hw' : i w = w := mem_fixV_zpowers.1 hw
      rw [hUy]
      refine ⟨m w, mem_fixV_zpowers.2 ?_, ?_⟩
      · rw [hym, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hw']
      · rw [← hg]
        rfl
    intro x hx
    have hx' : (g : G)⁻¹ * x * g ∈ Subgroup.centralizer (Uj : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
      have hc' := Subgroup.mem_centralizer_iff.1 hx _ (hgU u hu)
      calc u * ((g : G)⁻¹ * x * g) = (g : G)⁻¹ * ((g * u * (g : G)⁻¹) * x) * g := by group
        _ = (g : G)⁻¹ * (x * (g * u * (g : G)⁻¹)) * g := by rw [hc']
        _ = (g : G)⁻¹ * x * g * u := by group
    have h1 := M.mul_mem (M.mul_mem g.2.1 (hle hx')) (M.inv_mem g.2.1)
    rwa [show (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x by group] at h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := IsPGroup.of_card hV64
  set K' := Subgroup.centralizer (Uj : Set G) ⊔ T with hK'def
  have hUjC : Uj ≤ Subgroup.centralizer (Uj : Set G) := by
    intro u hu
    refine Subgroup.mem_centralizer_iff.2 fun u' hu' => ?_
    have := congrArg Subtype.val (mul_comm (⟨u', hUjV hu'⟩ : ↥V) ⟨u, hUjV hu⟩)
    simpa using this
  have hK'N : K' ≤ Subgroup.normalizer (Uj : Set G) :=
    sup_le (Subgroup.centralizer_le_normalizer _) hTUj
  have hUjO : Uj ≤ pCoreOf 2 K' := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hUjC.trans le_sup_left) hK'N (hV2.to_le hUjV)
  have hInH : InH T K' := by
    refine ⟨le_sup_right, fun hb => hS.z_ne_one ?_⟩
    have := hUjO hzUj
    rwa [hb, Subgroup.mem_bot] at this
  have hK'M : ¬ K' ≤ M := fun h => hUjM (le_sup_left.trans h)
  obtain ⟨H, hHs, hHK'⟩ := exists_isHStar_le hInH hK'M
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun x hx => ?_) hS.T_le_Gz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hx z hzUj).symm
  obtain ⟨-, -, hL1T⟩ := h23 G T L V t z hS H hHs (hHK'.trans hK'z)
  have hL1H : L1 T L V ≤ H := fun x hx => by
    have : x ∈ H ⊓ M := hL1T ▸ Subgroup.mem_sup_left hx
    exact this.1
  have hTC : T ≤ Subgroup.normalizer (Subgroup.centralizer (Uj : Set G) : Set G) := by
    intro s hs
    have h1 := mem_normalizer_inf_centralizer (M := ⊤) (Subgroup.mem_top s) (hTUj hs)
    rwa [top_inf_eq] at h1
  have hL1C : L1 T L V ≤ Subgroup.centralizer (Uj : Set G) := by
    rw [← hL1O]
    exact (oTwoUpper_mono (hL1H.trans hHK')).trans
      (oTwoUpper_le_of_pow_mem fun x hx => exists_pow_mem_of_mem_sup hS.hyp.hyp.sylow.1 hTC hx)
  have hUj3 : E3.mQuot V Uj = 3 := by
    have hcard : Nat.card Uj = 8 := by
      rw [hUjdef, Subgroup.card_map_of_injective V.subtype_injective, hci]
    have h1 := Subgroup.relIndex_mul_card (H := Uj) (K := V)
    rw [inf_of_le_left hUjV, hcard, hV64] at h1
    have h8 : Uj.relIndex V = 2 ^ 3 := by omega
    rw [E3.mQuot, h8, padicValNat.prime_pow]
  have hpow : ∀ x ∈ M ⊓ Subgroup.centralizer (Uj : Set G),
      ∃ k : ℕ, x ^ 2 ^ k ∈ M ⊓ Subgroup.centralizer (V : Set G) := by
    intro x hx
    rcases hd Uj hUjV hUj3 with hi | ⟨l, hl, -, -, hii⟩ |
        ⟨y', -, -, hy'2, -, i', hi', hact', hiii⟩
    · exact ⟨0, by rw [pow_zero, pow_one, ← hi]; exact hx⟩
    · have hlx : l * x * l⁻¹ ∈ M ⊓ Subgroup.centralizer
          ((Uj.map (MulAut.conj l).toMonoidHom : Subgroup G) : Set G) := by
        refine ⟨M.mul_mem (M.mul_mem (hLM hl) hx.1) (M.inv_mem (hLM hl)),
          Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
        obtain ⟨u', hu', rfl⟩ := hu
        have hc' := Subgroup.mem_centralizer_iff.1 hx.2 u' hu'
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc l * u' * l⁻¹ * (l * x * l⁻¹) = l * (u' * x) * l⁻¹ := by group
          _ = l * (x * u') * l⁻¹ := by rw [hc']
          _ = l * x * l⁻¹ * (l * u' * l⁻¹) := by group
      rw [hii] at hlx
      obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup (pCoreOf_isPGroup 2 _)
        (fun r hr => mem_normalizer_inf_centralizer (hR2 hr).1 (hR2 hr).2) hlx
      refine ⟨k, ?_⟩
      rw [conj_pow] at hk
      have hlN := mem_normalizer_inf_centralizer (M := M) (V := V) (hLM hl) (hLV hl)
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hlN) _).1 hk
      rwa [show l⁻¹ * (l * x ^ 2 ^ k * l⁻¹) * l⁻¹⁻¹ = x ^ 2 ^ k by group] at this
    · rw [hiii, sup_comm] at hx
      have hiN := mem_normalizer_inf_centralizer (M := M) (V := V) hi'.1 hi'.2
      have hi'2 : i' ^ 2 ∈ M ⊓ Subgroup.centralizer (V : Set G) := by
        refine ⟨M.pow_mem hi'.1 2, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
        have hy'sq : y' ^ 2 = 1 := by rw [← hy'2, pow_orderOf_eq_one]
        have e1 : ((y' (y' ⟨v, hv⟩) : ↥V) : G) = i' ^ 2 * v * (i' ^ 2)⁻¹ := by
          rw [hact', hact']
          simp only [sq, mul_inv_rev]
          group
        have e2 : y' (y' ⟨v, hv⟩) = ⟨v, hv⟩ := by
          rw [← MulAut.mul_apply, ← sq, hy'sq]
          rfl
        rw [e2] at e1
        have e3 : v = i' ^ 2 * v * (i' ^ 2)⁻¹ := e1
        calc v * i' ^ 2 = i' ^ 2 * v * (i' ^ 2)⁻¹ * i' ^ 2 := by rw [← e3]
          _ = i' ^ 2 * v := by group
      obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
        ((Subgroup.zpowers_le).2 hiN)).1 hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have hbN : i' ^ n ∈ Subgroup.normalizer
          ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := Subgroup.zpow_mem _ hiN n
      obtain ⟨a', ha', hae⟩ := A4.exists_pow_mul_eq ha hbN 2
      refine ⟨1, ?_⟩
      rw [pow_one, hae]
      refine Subgroup.mul_mem _ ha' ?_
      have e : (i' ^ n) ^ 2 = (i' ^ 2) ^ n := by
        rw [← zpow_natCast, ← zpow_natCast i' 2, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [e]
      exact Subgroup.zpow_mem _ hi'2 n
  have hL1V : L1 T L V ≤ M ⊓ Subgroup.centralizer (V : Set G) := by
    rw [← hL1O]
    exact (oTwoUpper_mono (le_inf (hL1L.trans hLM) hL1C)).trans (oTwoUpper_le_of_pow_mem hpow)
  have hL12 : IsPGroup 2 (L1 T L V) := by
    have h1 : L1 T L V ≤ pCoreOf 2 L := by
      rw [← hCL]
      exact le_inf hL1L fun x hx => (hL1V hx).2
    exact (pCoreOf_isPGroup 2 L).to_le h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hL12
  have h3 : 3 ∣ Nat.card (L1 T L V) := by
    rw [← hL13]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card (H := pCoreOf 2 (L1 T L V)) (K := L1 T L V))
  rw [hk] at h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by decide)

end CFSG.Quasithin.H13
