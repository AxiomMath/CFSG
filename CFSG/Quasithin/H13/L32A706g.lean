module

public import CFSG.Quasithin.H13.L32A706f
public import CFSG.Quasithin.EmptyFaithful.S145Facts
public import CFSG.Quasithin.H13.L32A706d

public section

namespace CFSG.Quasithin.H13.L32A.M76

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem exists_cube_not_mem (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : ∃ l ∈ l1 T L V, l ∉ pCoreOf 2 (l1 T L V) ∧ l ^ 3 = 1 := by
  by_contra hcon
  have hcon' : ∀ l ∈ l1 T L V, l ∉ pCoreOf 2 (l1 T L V) → l ^ 3 ≠ 1 :=
    fun l hl hlO h3 => hcon ⟨l, hl, hlO, h3⟩
  have hle : l1 T L V ≤ pCoreOf 2 (l1 T L V) := (Subgroup.closure_le _).mpr fun x hx => by
    have hxL : x ∈ l1 T L V := Subgroup.subset_closure hx
    by_contra hxO
    exact hcon' x hxL hxO (l1_cube_eq_one S h1222 h1332 h1334 hxL hx.2)
  have h3 := (relIndex_l1_T S h1222 h1332 h1334).1
  rw [Subgroup.relIndex_eq_one.mpr hle] at h3
  norm_num at h3

theorem false_of_caseI (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h98 : HypF98 T V L (fsuV1 T V) V H) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {Y : Subgroup G} (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (hHYL : H = Y ⊔ (l1 T L V ⊔ T)) (hexp : ∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y)
    (hYlt : pCoreOf 2 Y < Y)
    (hI : ∀ A ∈ @QhatStar _ (commGroupOfElemAbelian h98.toHypF91.isElemAbelian_tilde) _
        (autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H))),
      ∀ a ∈ A, ∀ y : ↥H, (y : G) ∈ Y →
        a * FixR.rho h98.toHypF91 y = FixR.rho h98.toHypF91 y * a) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h91 := h98.toHypF91
  have hE := h91.isElemAbelian_tilde
  let _ : CommGroup ↥(tildeOf (fsuV1 T V) (conjClosure V H)) := commGroupOfElemAbelian hE
  have : Finite (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :=
    Finite.of_injective _ MulEquiv.toEquiv_injective
  set ρ := FixR.rho h91 with hρ
  set X := autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) with hX
  set R := pCoreOf 2 (l1 T L V ⊔ T) with hR
  set Rb := autOn (tildeOf (fsuV1 T V) R) (tildeOf (fsuV1 T V) (conjClosure V H)) with hRb
  have hYH : Y ≤ H := hHYL ▸ le_sup_left
  have hTH := Setting147.TH' S
  have hL1H := Setting147.l1H' S
  have hRT : R ≤ T := Setting147.R1_le_T S
  have hRH : R ≤ H := hRT.trans hTH
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le151 S.hyp.fsu.sylow hTH
  have h2 := (relIndex_l1_T S h1222 h1332 h1334).2
  have hOR : pCoreOf 2 (l1 T L V) ≤ R := pCoreOf_l1_le_R1 S h1332
  have hρX : ∀ x : ↥H, ρ x ∈ X := fun x =>
    (FixR.mem_autOn_tilde_iff h91 le_rfl).mpr ⟨x, x.2, rfl⟩
  have hV : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure V H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hE.2 w w.2)
  have hidx : (R.subgroupOf T).index = 2 := h2
  have hidx2 : ∀ s ∈ T, ∀ t ∈ T, s ∉ R → t ∉ R → t⁻¹ * s ∈ R := by
    intro s hs t ht hsR htR
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨t, ht⟩ : ↥T)⁻¹)
      (b := ⟨s, hs⟩)).mpr ⟨fun h => absurd (by
        simpa using Subgroup.mem_subgroupOf.mp (inv_mem h)) htR,
        fun h => absurd (Subgroup.mem_subgroupOf.mp h) hsR⟩
    simpa using Subgroup.mem_subgroupOf.mp this
  have hsq : ∀ t ∈ T, t * t ∈ R := by
    intro t ht
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨t, ht⟩ : ↥T))
      (b := ⟨t, ht⟩)).mpr Iff.rfl
    simpa using Subgroup.mem_subgroupOf.mp this
  have hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ) :=
    (qhatOf_le_qOf X).trans h98.lemma_14_5_18_three.1
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hq)
  have hr2 : r ≤ 2 := by rw [← hr] at hq; exact_mod_cast hq
  obtain ⟨A₀, hA₀⟩ := QhatStar_nonempty hr.symm hr2
  obtain ⟨x, hx⟩ := exists_conj_le h91 hTsyl (QhatStar_le hA₀) (isPGroup_of_mem_QhatStar_aux hA₀)
  set A := conjBy (ρ x)⁻¹ A₀ with hA
  have hAQ : A ∈ QhatStar X := conjBy_mem_QhatStar hA₀ (X.inv_mem (hρX x))
  have hAT : ∀ a ∈ A, ∃ s : ↥H, (s : G) ∈ T ∧ ρ s = a := by
    intro a ha
    rw [hA, mem_conjBy_iff, inv_inv] at ha
    have h1 := hx _ ha
    rw [show (ρ x)⁻¹ * (ρ x * a * (ρ x)⁻¹) * ρ x = a by group] at h1
    exact (FixR.mem_autOn_tilde_iff h91 hTH).mp h1
  have hKY : l1 T L V ⊔ T ≤ Subgroup.normalizer (Y : Set G) := (sup_le hL1H hTH).trans hHY
  have hdecomp : ∀ h : ↥H, ∃ y : ↥H, (y : G) ∈ Y ∧ ∃ k : ↥H, (k : G) ∈ l1 T L V ⊔ T ∧
      h = y * k := by
    intro h
    obtain ⟨y, hy, k, hk, hyk⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hKY).mp (hHYL ▸ h.2 : (h : G) ∈ Y ⊔ _)
    exact ⟨⟨y, hYH hy⟩, hy, ⟨k, (sup_le hL1H hTH) hk⟩, hk, Subtype.ext hyk⟩
  have hAR : ∀ s : ↥H, (s : G) ∈ R → ρ s ∈ A → ρ s = 1 := by
    intro s hsR hsA
    set N := X ⊓ ⨅ g : ↥X, conjBy (g : MulAut _)⁻¹ Rb with hN
    have hmemN : ∀ c, c ∈ N ↔ c ∈ X ∧ ∀ g ∈ X, g * c * g⁻¹ ∈ Rb := by
      intro c
      rw [hN, Subgroup.mem_inf, Subgroup.mem_iInf]
      refine and_congr Iff.rfl ⟨fun h g hg => ?_, fun h g => ?_⟩
      · have := h ⟨g, hg⟩
        rwa [mem_conjBy_iff, inv_inv] at this
      · rw [mem_conjBy_iff, inv_inv]
        exact h g g.2
    have hNX : N ≤ X := inf_le_left
    have hXN : X ≤ Subgroup.normalizer (N : Set _) := by
      intro h hh
      refine Subgroup.mem_normalizer_fintype fun c hc => ?_
      obtain ⟨hcX, hc⟩ := (hmemN c).mp hc
      refine (hmemN _).mpr ⟨X.mul_mem (X.mul_mem hh hcX) (X.inv_mem hh), fun g hg => ?_⟩
      have := hc (g * h) (X.mul_mem hg hh)
      rwa [show g * h * c * (g * h)⁻¹ = g * (h * c * h⁻¹) * g⁻¹ by group] at this
    have hRb2 : IsPGroup 2 Rb := by
      rintro ⟨a, ha⟩
      obtain ⟨z, hzR, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 hRH).mp ha
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (l1 T L V ⊔ T) ⟨z, hzR⟩
      refine ⟨k, Subtype.ext ?_⟩
      have hzk : z ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      simp [← map_pow, hzk]
    have hN2 : IsPGroup 2 N := hRb2.to_le fun c hc => by
      have := ((hmemN c).mp hc).2 1 X.one_mem
      simpa using this
    have hNbot : N = ⊥ := eq_bot_iff.mpr ((le_pCoreOf_of_le_normalizer 2 hNX hXN hN2).trans
      (pCoreOf_autOn_eq_bot' h91).le)
    have hsN : ρ s ∈ N := by
      refine (hmemN _).mpr ⟨hρX s, fun g hg => ?_⟩
      obtain ⟨h, -, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 le_rfl).mp hg
      obtain ⟨y, hy, k, hk, rfl⟩ := hdecomp h
      have hb : ρ k * ρ s * (ρ k)⁻¹ ∈ conjBy (ρ k) A := by
        rw [mem_conjBy_iff]; group; exact hsA
      have hc := hI _ (conjBy_mem_QhatStar hAQ (hρX k)) _ hb y hy
      have e : ρ (y * k) * ρ s * (ρ (y * k))⁻¹ = ρ (k * s * k⁻¹) := by
        rw [map_mul, map_mul, map_mul, map_inv, mul_inv_rev]
        calc ρ y * ρ k * ρ s * ((ρ k)⁻¹ * (ρ y)⁻¹)
            = ρ y * (ρ k * ρ s * (ρ k)⁻¹) * (ρ y)⁻¹ := by group
          _ = ρ k * ρ s * (ρ k)⁻¹ := by rw [← hc]; group
      rw [e]
      exact (FixR.mem_autOn_tilde_iff h91 hRH).mpr ⟨k * s * k⁻¹, by
        simpa using (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hk) s).mp hsR, rfl⟩
    rw [hNbot] at hsN
    exact hsN
  obtain ⟨⟨u, huA⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (ne_bot_of_mem_QhatStar216 hAQ)
  obtain ⟨t, htT, rfl⟩ := hAT u huA
  have hu1' : ρ t ≠ 1 := fun h => hu1 (Subtype.ext h)
  have htR : (t : G) ∉ R := fun h => hu1' (hAR t h huA)
  have hu2 : ρ t ^ 2 = 1 := by
    rw [← map_pow]
    exact hAR _ (by simpa [pow_two] using hsq t htT) (by rw [map_pow]; exact A.pow_mem huA 2)
  have hAeq : A = Subgroup.zpowers (ρ t) := by
    refine le_antisymm (fun a ha => ?_) (Subgroup.zpowers_le.mpr huA)
    obtain ⟨s, hsT, rfl⟩ := hAT a ha
    by_cases hsR : (s : G) ∈ R
    · rw [hAR s hsR ha]; exact Subgroup.one_mem _
    · have hts := hidx2 _ hsT _ htT hsR htR
      have h1 := hAR (t⁻¹ * s) (by simpa using hts) (by
        rw [map_mul, map_inv]; exact A.mul_mem (A.inv_mem huA) ha)
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      rw [← h1]; exact Subgroup.mem_zpowers _
  have hrk :
      rk ((⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))).map (commHom (ρ t))) ≤ 2 := by
    obtain ⟨r', hr', -, ⟨⟨-, hAr⟩, -⟩, -⟩ := QhatStar_spec hAQ
    have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr.symm)
    have hcard : Nat.card A = 2 := by
      rw [hAeq, Nat.card_zpowers, orderOf_eq_prime hu2 hu1']
    have hrkA : rk A = 1 := by
      show padicValNat 2 (Nat.card A) = 1
      rw [hcard]; simp
    rw [rAV, hrkA, hAeq, rkIdx_fixV_zpowers, commV_zpowers_eq_map, hrr] at hAr
    have : ((rk ((⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))).map (commHom (ρ t))) :
      ℕ) : ℚ) ≤ 2 := by simpa using hAr.le.trans hr2
    exact_mod_cast this
  have hc : ∀ l : ↥H, (l : G) ∈ l1 T L V → (l : G) ^ 3 = 1 → ∀ y : ↥H, (y : G) ∈ Y →
      ρ l * ρ y = ρ y * ρ l := by
    intro l hl hl3 y hy
    by_cases hlO : (l : G) ∈ pCoreOf 2 (l1 T L V)
    · obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 (l1 T L V) ⟨l, hlO⟩
      have hj' : (l : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have hl1 : (l : G) = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hl3)
          (Nat.Coprime.pow_right j (by norm_num))) (orderOf_dvd_of_pow_eq_one hj'))
      have : l = 1 := Subtype.ext hl1
      rw [this, map_one, one_mul, mul_one]
    have ho := conj_mul_mem_of_not_mem S h1222 h1332 h1334 htT htR hl hlO
    set c := ρ t * (ρ l * ρ t * (ρ l)⁻¹) with hcdef
    have hcY : ∀ y' : ↥H, (y' : G) ∈ Y → c * ρ y' = ρ y' * c := by
      intro y' hy'
      have h1 := hI A hAQ _ huA y' hy'
      have hmem : ρ l * ρ t * (ρ l)⁻¹ ∈ conjBy (ρ l) A := by
        rw [mem_conjBy_iff]; group; exact huA
      have h2 := hI _ (conjBy_mem_QhatStar hAQ (hρX l)) _ hmem y' hy'
      rw [hcdef, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
    obtain ⟨rr, hrr⟩ : ∃ rr : ↥H, rr = l⁻¹ * t * (l * t * l⁻¹) := ⟨_, rfl⟩
    have hrrR : (rr : G) ∈ R := by
      have e : (rr : G) = ((l : G)⁻¹ * ((t : G) * l * (t : G)⁻¹ * l) * l) * ((l : G) ^ 3)⁻¹ *
          (l * ((t : G) * t) * (l : G)⁻¹) := by
        simp only [hrr, Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [e, hl3, inv_one, mul_one]
      refine R.mul_mem (hOR ?_) ?_
      · simpa using (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (inv_mem hl)) _).mp
          ho
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _
          (Subgroup.mem_sup_left hl)) _).mp (hsq t htT)
    obtain ⟨b, hb⟩ : ∃ b, b = (ρ rr)⁻¹ := ⟨_, rfl⟩
    have hab : ρ l = c * b := by
      rw [hb, hcdef, hrr, map_mul, map_mul, map_mul, map_mul, map_inv]; group
    have hconj : ∀ y' : ↥H, (y' : G) ∈ Y → ρ l * ρ y' * (ρ l)⁻¹ = b * ρ y' * b⁻¹ := by
      intro y' hy'
      have hbY : b * ρ y' * b⁻¹ = ρ (rr⁻¹ * y' * rr) := by
        rw [hb, map_mul, map_mul, map_inv, inv_inv]
      have hY' : ((rr⁻¹ * y' * rr : ↥H) : G) ∈ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (hHY (rr⁻¹).2) y').mp hy'
        simpa [mul_assoc] using this
      rw [hab]
      calc c * b * ρ y' * (c * b)⁻¹ = c * (b * ρ y' * b⁻¹) * c⁻¹ := by group
        _ = c * ρ (rr⁻¹ * y' * rr) * c⁻¹ := by rw [hbY]
        _ = ρ (rr⁻¹ * y' * rr) := by rw [hcY _ hY']; group
        _ = b * ρ y' * b⁻¹ := hbY.symm
    have hpow : ∀ n : ℕ, ∀ y' : ↥H, (y' : G) ∈ Y →
        ρ l ^ n * ρ y' * (ρ l ^ n)⁻¹ = b ^ n * ρ y' * (b ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro y' _; simp
      | succ n ih =>
        intro y' hy'
        have hY' : ((rr⁻¹ * y' * rr : ↥H) : G) ∈ Y := by
          have := (Subgroup.mem_normalizer_iff.mp (hHY (rr⁻¹).2) y').mp hy'
          simpa [mul_assoc] using this
        have hbY : b * ρ y' * b⁻¹ = ρ (rr⁻¹ * y' * rr) := by
          rw [hb, map_mul, map_mul, map_inv, inv_inv]
        calc ρ l ^ (n + 1) * ρ y' * (ρ l ^ (n + 1))⁻¹
            = ρ l ^ n * (ρ l * ρ y' * (ρ l)⁻¹) * (ρ l ^ n)⁻¹ := by rw [pow_succ]; group
          _ = ρ l ^ n * ρ (rr⁻¹ * y' * rr) * (ρ l ^ n)⁻¹ := by rw [hconj y' hy', hbY]
          _ = b ^ n * ρ (rr⁻¹ * y' * rr) * (b ^ n)⁻¹ := ih _ hY'
          _ = b ^ (n + 1) * ρ y' * (b ^ (n + 1))⁻¹ := by rw [← hbY, pow_succ]; group
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 (l1 T L V ⊔ T) ⟨rr, hrrR⟩
    have hrrm : rr ^ 2 ^ m = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
    have hbm : b ^ 2 ^ m = 1 := by rw [hb, inv_pow, ← map_pow, hrrm, map_one, inv_one]
    have h1 : Commute (ρ l ^ 2 ^ m) (ρ y) := by
      have := hpow (2 ^ m) y hy
      rw [hbm, one_mul, inv_one, mul_one] at this
      exact (mul_inv_eq_iff_eq_mul.mp this)
    have h3 : ρ l ^ 3 = 1 := by
      rw [← map_pow]; exact congrArg ρ (Subtype.ext hl3) |>.trans (map_one _)
    have hmem : ρ l ∈ Subgroup.zpowers (ρ l ^ 2 ^ m) :=
      A4.mem_zpowers_pow_of_coprime (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h3)
        (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3)))
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hj]
    exact (h1.zpow_left j).eq
  have hHL := H_le_N_l1_of_comm S h1222 h1332 h1334 h91 hHY hHYL hc
  obtain ⟨l₀, hl₀, hl₀O, hl₀3⟩ := exists_cube_not_mem S h1222 h1332 h1334
  have hl₀H : l₀ ∈ H := hL1H hl₀
  have hOQ : pCoreOf 2 (l1 T L V) ≤ pCoreOf 2 H := by
    rw [← Setting147.inf_O2H S hHL]; exact inf_le_left
  have hl3 : ρ ⟨l₀, hl₀H⟩ ^ 3 = 1 := by
    rw [← map_pow]
    exact (congrArg ρ (Subtype.ext hl₀3 : (⟨l₀, hl₀H⟩ : ↥H) ^ 3 = 1)).trans (map_one _)
  have hinv : ρ t * ρ ⟨l₀, hl₀H⟩ * (ρ t)⁻¹ = (ρ ⟨l₀, hl₀H⟩)⁻¹ := by
    have ho := conj_mul_mem_of_not_mem S h1222 h1332 h1334 htT htR hl₀ hl₀O
    have h1 := (FixR.rho_eq_one_iff h91 (t * ⟨l₀, hl₀H⟩ * t⁻¹ * ⟨l₀, hl₀H⟩)).mpr
      (hOQ (by simpa using ho))
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hlfix : fixV (Subgroup.zpowers (ρ ⟨l₀, hl₀H⟩)) = ⊥ := by
    refine eq_bot_iff.mpr fun w hw => ?_
    rw [mem_fixV_zpowers_iff] at hw
    exact rho_fix_eq_one S h1222 h1332 h1334 h91 hHL hl₀ hl₀O w hw
  have hYQ : pCoreOf 2 Y = Y ⊓ pCoreOf 2 H := S152Y.pCoreOf_eq_inf_of_normalizer hYH hHY
  obtain ⟨y₀, hy₀Y, hy₀O⟩ := IsConcreteLE.exists_of_lt hYlt
  have hyp : ρ ⟨y₀, hYH hy₀Y⟩ ^ p = 1 := by
    rw [← map_pow]
    refine (FixR.rho_eq_one_iff h91 _).mpr ?_
    have := hexp y₀ hy₀Y
    rw [hYQ] at this
    simpa using this.2
  have hy1 : ρ ⟨y₀, hYH hy₀Y⟩ ≠ 1 := fun h => hy₀O (by
    rw [hYQ]; exact ⟨hy₀Y, (FixR.rho_eq_one_iff h91 _).mp h⟩)
  have hyl := (hc ⟨l₀, hl₀H⟩ hl₀ hl₀3 ⟨y₀, hYH hy₀Y⟩ hy₀Y).symm
  have hyu := (hI A hAQ _ huA ⟨y₀, hYH hy₀Y⟩ hy₀Y).symm
  exact false_of_inverted_three hV hp hp5 hu2 hl3 hinv hlfix hrk hyp hy1 hyl hyu

end CFSG.Quasithin.H13.L32A.M76
