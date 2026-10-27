module

public import CFSG.Quasithin.EmptyFaithful.S146Three
public import CFSG.Quasithin.EmptyFaithful.S145Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Algebra

variable {G : Type} [Group G]

theorem S146T.mul_inv_mem_of_card {V Z : Subgroup G} (hZV : Z ≤ V) (hV : Nat.card V = 4)
    (hZ : Nat.card Z = 2) {a b : G} (ha : a ∈ V) (hb : b ∈ V) (haZ : a ∉ Z) (hbZ : b ∉ Z) :
    a * b⁻¹ ∈ Z := by
  have hcard : Nat.card (Z.subgroupOf V) = 2 := by
    rw [← hZ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
  have hidx : (Z.subgroupOf V).index = 2 := by
    have h := Subgroup.card_mul_index (Z.subgroupOf V)
    rw [hcard, hV] at h
    omega
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.mp hidx
  have key : ∀ x : V, (x : G) ∉ Z → x * c ∈ Z.subgroupOf V := by
    intro x hx
    rcases hc x with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd (Subgroup.mem_subgroupOf.mp h1) hx
  have h1 := key ⟨a, ha⟩ haZ
  have h2 := key ⟨b, hb⟩ hbZ
  have h3 := (Z.subgroupOf V).mul_mem h1 ((Z.subgroupOf V).inv_mem h2)
  have e : (⟨a, ha⟩ * c) * (⟨b, hb⟩ * c)⁻¹ = (⟨a, ha⟩ * ⟨b, hb⟩⁻¹ : V) := by group
  rw [e] at h3
  exact Subgroup.mem_subgroupOf.mp h3

end Algebra

section Setting

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem S146T.conj_Z {q z : G} (hq : q ∈ mcOf T) (hz : z ∈ quasithinOmegaOneCenter T) :
    q * z * q⁻¹ = z := by
  rw [S146T.comm_Z hq hz]; group

theorem Setting146.conj_mem_mul_Z (S : Setting146 G T M) {t v : G} (ht : t ∈ T)
    (hv : v ∈ VZ T M) : t * v * t⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T := by
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  by_cases hvZ : v ∈ quasithinOmegaOneCenter T
  · have : t * v * t⁻¹ * v⁻¹ = 1 := by rw [S146T.comm_Z_T ht hvZ]; group
    rw [this]
    exact Subgroup.one_mem _
  · have hy : t * v * t⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_V ht) v).mp hv
    have hyZ : t * v * t⁻¹ ∉ quasithinOmegaOneCenter T := by
      intro h
      apply hvZ
      have e := S146T.comm_Z_T (T.inv_mem ht) h
      have hvy : v = t * v * t⁻¹ := by
        calc v = t⁻¹ * (t * v * t⁻¹) * t := by group
          _ = (t * v * t⁻¹) * t⁻¹ * t := by rw [e]
          _ = t * v * t⁻¹ := by group
      exact hvy ▸ h
    exact S146T.mul_inv_mem_of_card hZV S.hyp.rank_two S.card_Z hy hv hyZ hvZ

theorem Setting146.exists_mem_inf_centralizer_not_le (S : Setting146 G T M) {H' : Subgroup G}
    (hH' : IsHTM T M H') {u : G} (hu : u ∈ conjClosure (VZ T M) H')
    (hQ : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 H')
    (h2 : ⁅conjClosure (VZ T M) H', pCoreOf 2 H'⁆ = quasithinOmegaOneCenter T) {t : G}
    (htT : t ∈ T)
    (hnc : u * (t * u * t⁻¹) ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G)) :
    ∃ x ∈ pCoreOf 2 H' ⊓ Subgroup.centralizer ({u} : Set G),
      x ∉ Subgroup.centralizer (VZ T M : Set G) := by
  by_contra hcon
  push Not at hcon
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H') := S.lemma_14_5_15_two hH'
  have hQH' : pCoreOf 2 H' ≤ H' := pCoreOf_le 2 H'
  have hH'G : H' ≤ mcOf T := S.le_mcOf hH'
  have hVU : VZ T M ≤ conjClosure (VZ T M) H' := le_conjClosure _ _
  have hZmem : ∀ q ∈ pCoreOf 2 H', ∀ w ∈ conjClosure (VZ T M) H',
      ⁅q, w⁆ ∈ quasithinOmegaOneCenter T := fun q hq w hw => S.comm_mem_Z hH' hw hq
  have hqG : ∀ q ∈ pCoreOf 2 H', q ∈ mcOf T := fun q hq => hH'G (hQH' hq)
  have hwG : ∀ w ∈ conjClosure (VZ T M) H', w ∈ mcOf T :=
    fun w hw => S.mem_mcOf_of_mem_conjClosure hH' hw
  obtain ⟨v, hvV, q₀, hq₀, hvq₀⟩ : ∃ v ∈ VZ T M, ∃ q₀ ∈ pCoreOf 2 H', ¬ (q₀ * v = v * q₀) := by
    by_contra hno
    push Not at hno
    have hUc : conjClosure (VZ T M) H' ≤ Subgroup.centralizer (pCoreOf 2 H' : Set G) := by
      refine conjClosure_le fun h hh w hw => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqh : h⁻¹ * q * h ∈ pCoreOf 2 H' := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H' (H'.inv_mem hh)) q).mp hq
        simpa using this
      have hcomm := hno w hw _ hqh
      calc q * (h * w * h⁻¹) = h * ((h⁻¹ * q * h) * w) * h⁻¹ := by group
        _ = h * (w * (h⁻¹ * q * h)) * h⁻¹ := by rw [hcomm]
        _ = (h * w * h⁻¹) * q := by group
    have hbot : ⁅conjClosure (VZ T M) H', pCoreOf 2 H'⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUc
    rw [h2] at hbot
    have h1 : 1 < Nat.card (quasithinOmegaOneCenter T) := by rw [S.card_Z]; norm_num
    exact absurd hbot ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
  have hvU : v ∈ conjClosure (VZ T M) H' := hVU hvV
  have hker : ∀ q ∈ pCoreOf 2 H', ⁅q, u⁆ = 1 → ⁅q, v⁆ = 1 := by
    intro q hq h1
    have hqC : q ∈ pCoreOf 2 H' ⊓ Subgroup.centralizer ({u} : Set G) :=
      ⟨hq, Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff.mp hx]; exact S146T.comm_eq_one_iff.mp h1⟩
    exact S146T.comm_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mp (hcon q hqC) v hvV)
  have hc0 : ⁅q₀, u⁆ ≠ 1 := fun h1 =>
    hvq₀ (S146T.comm_eq_one_iff.mp (hker q₀ hq₀ h1)).symm
  have hd0 : ⁅q₀, v⁆ ≠ 1 := fun h1 => hvq₀ (S146T.comm_eq_one_iff.mp h1).symm
  have hcd : ⁅q₀, u⁆ = ⁅q₀, v⁆ :=
    S.Z_eq_of_iff (hZmem q₀ hq₀ u hu) (hZmem q₀ hq₀ v hvU)
      ⟨fun h => absurd h hc0, fun h => absurd h hd0⟩
  have hW : u * v ∈ Subgroup.centralizer (pCoreOf 2 H' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q₁ hq₁
    have ha := hZmem q₁ hq₁ u hu
    have hb := hZmem q₁ hq₁ v hvU
    have hprod : ⁅q₁, u * v⁆ = ⁅q₁, u⁆ * ⁅q₁, v⁆ := by
      rw [S146T.comm_mul_right, S146T.conj_Z (hwG u hu) hb]
    suffices h : ⁅q₁, u * v⁆ = 1 from (S146T.comm_eq_one_iff.mp h).symm
    rw [hprod]
    by_cases ha1 : ⁅q₁, u⁆ = 1
    · rw [ha1, hker q₁ hq₁ ha1, one_mul]
    · have hac : ⁅q₁, u⁆ = ⁅q₀, u⁆ :=
        S.Z_eq_of_iff ha (hZmem q₀ hq₀ u hu) ⟨fun h => absurd h ha1, fun h => absurd h hc0⟩
      have hmulu : ⁅q₁ * q₀, u⁆ = 1 := by
        rw [S146T.comm_mul_left, S146T.conj_Z (hqG q₁ hq₁) (hZmem q₀ hq₀ u hu), ← hac]
        have := S146T.Z_sq ha
        rwa [sq] at this
      have hmulv := hker (q₁ * q₀) ((pCoreOf 2 H').mul_mem hq₁ hq₀) hmulu
      rw [S146T.comm_mul_left, S146T.conj_Z (hqG q₁ hq₁) (hZmem q₀ hq₀ v hvU)] at hmulv
      rw [hac, hcd]
      exact hmulv
  have hVt : t * v * t⁻¹ ∈ VZ T M :=
    (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_V htT) v).mp hvV
  have hζ : t * v * t⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T := S.conj_mem_mul_Z htT hvV
  have hutU : t * u * t⁻¹ ∈ conjClosure (VZ T M) H' :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure (VZ T M) H' (hH'.1.1 htT)) u).mp hu
  have hWt : t * (u * v) * t⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqt : t⁻¹ * q * t ∈ pCoreOf 2 H' := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H' (H'.inv_mem (hH'.1.1 htT))) q).mp hq
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.mp hW _ hqt
    calc q * (t * (u * v) * t⁻¹) = t * ((t⁻¹ * q * t) * (u * v)) * t⁻¹ := by group
      _ = t * ((u * v) * (t⁻¹ * q * t)) * t⁻¹ := by rw [hcomm]
      _ = t * (u * v) * t⁻¹ * q := by group
  have hζC : t * v * t⁻¹ * v⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H' : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq => S146T.comm_Z (hqG q hq) hζ
  have hvw : v * (t * u * t⁻¹) = (t * u * t⁻¹) * v := isElemAbelian_comm hUab hvU hutU
  have hvy : v * (t * v * t⁻¹) = (t * v * t⁻¹) * v :=
    isElemAbelian_comm hUab hvU (hVU hVt)
  have hvv : v * v = 1 := by
    have := isElemAbelian_pow_eq_one hUab hvU
    rwa [sq] at this
  have hid : (u * v) * (t * (u * v) * t⁻¹) * (t * v * t⁻¹ * v⁻¹)⁻¹ = u * (t * u * t⁻¹) := by
    have e1 : (u * v) * (t * (u * v) * t⁻¹) * (t * v * t⁻¹ * v⁻¹)⁻¹ =
        u * (v * (t * u * t⁻¹)) * ((t * v * t⁻¹) * v * (t * v * t⁻¹)⁻¹) := by group
    have e2 : (t * v * t⁻¹) * v * (t * v * t⁻¹)⁻¹ = v := by
      rw [← hvy]; group
    rw [e1, hvw, e2]
    calc u * ((t * u * t⁻¹) * v) * v = u * (t * u * t⁻¹) * (v * v) := by group
      _ = u * (t * u * t⁻¹) := by rw [hvv, mul_one]
  have hmem : u * (t * u * t⁻¹) ∈ Subgroup.centralizer (pCoreOf 2 H' : Set G) := by
    rw [← hid]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hW hWt) (Subgroup.inv_mem _ hζC)
  exact hnc (Subgroup.centralizer_le (fun x hx => hQ hx) hmem)

end Setting

section Three

open S1421

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.yOfL22_eq_commutator (S : Setting146 G T M) {B : Subgroup G} (hBT : B ≤ T)
    {x : G} (hxB : x ∈ B) (hxV : x ∉ Subgroup.centralizer (VZ T M : Set G)) :
    ⁅yOfL22 T M, B⁆ = yOfL22 T M := by
  obtain ⟨e⟩ := S.facts.sThree
  set Y := yOfL22 T M with hYdef
  have hYP : Y ≤ Y ⊔ T := le_sup_left
  have hTP : T ≤ Y ⊔ T := le_sup_right
  have hTsyl : IsSylowTwoOf T (Y ⊔ T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTP
  have hQYT : pCoreOf 2 (Y ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  obtain ⟨y0, hy0, hy0G⟩ : ∃ y0 ∈ Y, y0 ∉ mcOf T := by
    by_contra hcon
    push Not at hcon
    exact S.not_yOfL22_le_mcOf hcon
  have hxT : x ∈ T := hBT hxB
  set a := psi e ⟨y0, hYP hy0⟩ with ha
  set b := psi e ⟨x, hTP hxT⟩ with hb
  have ha1 : a ≠ 1 := by
    intro h
    exact hy0G (le_centralizer_quasithinOmegaOneCenter T
      (hQYT ((psi_eq_one_iff e (hYP hy0)).mp h)))
  have hb1 : b ≠ 1 := by
    intro h
    have hxP := (psi_eq_one_iff e (hTP hxT)).mp h
    rw [← S.facts.centralizer_yT] at hxP
    exact hxV hxP.2
  have ha3 : a ^ 3 = 1 := psi_y_pow_three e hy0
  have hb2 : b ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := S.hyp.sylow.1 ⟨x, hxT⟩
    have hk' : (⟨x, hTP hxT⟩ : ↥(Y ⊔ T)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    refine perm3_two (k := k) ?_
    rw [hb, ← map_pow, hk', map_one]
  have hne : a * b ≠ b * a := fun hcomm => by
    rcases perm3_comm ha3 hb2 hcomm with h | h
    · exact ha1 h
    · exact hb1 h
  have hCY : ⁅Y, B⁆ ≤ Y :=
    commutator_le_left_of_le_normalizer (fun z hz => T_le_normalizer_y S.hyp (hBT hz))
  have hinv := perm3_inv ha3 hb2 hne
  have hcomm : ⁅a, b⁆ = a ^ 2 := by
    have : ⁅a, b⁆ = a * (b * a * b⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [this, hinv, inv_inv, sq]
  have hb03 : (a ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ha3, one_pow]
  have hb01 : a ^ 2 ≠ 1 := by
    intro h2
    apply ha1
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha3, h2]; simp
  set c0 := ⁅y0, x⁆ with hc0
  have hc0C : c0 ∈ ⁅Y, B⁆ := Subgroup.commutator_mem_commutator hy0 hxB
  have hc0P : c0 ∈ Y ⊔ T := hYP (hCY hc0C)
  have hpc0 : psi e ⟨c0, hc0P⟩ = a ^ 2 := by
    have e1 : psi e ⟨c0, hc0P⟩ = ⁅a, b⁆ := psi_commutator e (hYP hy0) (hTP hxT)
    rw [e1, hcomm]
  have hrep : ∀ y ∈ Y, ∃ c ∈ ⁅Y, B⁆, ∃ o ∈ Y, (∃ m : ℕ, o ^ 2 ^ m = 1) ∧ y = c * o := by
    intro y hy
    have hyP : y ∈ Y ⊔ T := hYP hy
    have hy3 := psi_y_pow_three e hy
    obtain ⟨c, hcC, hpc⟩ : ∃ c ∈ ⁅Y, B⁆, ∃ hcP : c ∈ Y ⊔ T,
        psi e ⟨c, hcP⟩ = psi e ⟨y, hyP⟩ := by
      rcases perm3_gen hy3 hb03 hb01 with h1 | h1 | h1
      · exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, by rw [h1]; exact map_one _⟩
      · exact ⟨c0, hc0C, hc0P, by rw [hpc0, h1]⟩
      · refine ⟨c0 ^ 2, Subgroup.pow_mem _ hc0C 2, Subgroup.pow_mem _ hc0P 2, ?_⟩
        have : (⟨c0 ^ 2, Subgroup.pow_mem _ hc0P 2⟩ : ↥(Y ⊔ T)) = ⟨c0, hc0P⟩ ^ 2 := rfl
        rw [this, map_pow, hpc0, h1]
    obtain ⟨hcP, hpc⟩ := hpc
    have hcY : c ∈ Y := hCY hcC
    have hoY : c⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem hcY) hy
    have hoP : c⁻¹ * y ∈ Y ⊔ T := hYP hoY
    have hpo : psi e ⟨c⁻¹ * y, hoP⟩ = 1 := by
      have : (⟨c⁻¹ * y, hoP⟩ : ↥(Y ⊔ T)) = ⟨c, hcP⟩⁻¹ * ⟨y, hyP⟩ := rfl
      rw [this, map_mul, map_inv, hpc, inv_mul_cancel]
    have hoO : c⁻¹ * y ∈ pCoreOf 2 Y := by
      rw [pCoreOf_y_eq_inf S.facts]
      exact ⟨hoY, (psi_eq_one_iff e hoP).mp hpo⟩
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 Y ⟨c⁻¹ * y, hoO⟩
    refine ⟨c, hcC, c⁻¹ * y, hoY, ⟨m, ?_⟩, by group⟩
    simpa using congrArg Subtype.val hm
  exact eq_of_forall_mul_two_element hCY le_normalizer_commutator_left'
    (oTwoUpper_yOfL22 T M) hrep

theorem Setting146.stage1463_three (h1413 : StageLemma1413) (S : Setting146 G T M)
    {H : Subgroup G} (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) :
    ¬ (pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G) ≤
        Subgroup.centralizer (VZ T M : Set G)) ∧
      yOfL22 T M = ⁅yOfL22 T M, pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G)⁆ ∧
      yOfL22 T M = ⁅yOfL22 T M, pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G)⁆ := by
  obtain ⟨t, htT, htT0⟩ : ∃ t ∈ T, t ∉ tZero T u := by
    by_contra hcon
    push Not at hcon
    have h1 : (tZero T u).relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hcon
    have h2 := hu.index_two
    omega
  have hnc := hu.not_central_mul t htT htT0
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hQT : pCoreOf 2 H ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hH.1.1)
  obtain ⟨xH, hxH, hxHV⟩ := S.exists_mem_inf_centralizer_not_le hH hu.mem
    (S.pCoreOf_mcOf_le_pCoreOf hH) (S.lemma_14_5_21_two h1413 hH) htT hnc
  have huG : u ∈ conjClosure (VZ T M) (mcOf T) :=
    (conjClosure_le fun h hh w hw => Subgroup.subset_closure ⟨h, hHG hh, w, hw, rfl⟩ :
      conjClosure (VZ T M) H ≤ conjClosure (VZ T M) (mcOf T)) hu.mem
  obtain ⟨x1, hx1, hx1V⟩ := S.exists_mem_inf_centralizer_not_le S.isHTM_mcOf huG le_rfl
    (S.lemma_14_5_21_two h1413 S.isHTM_mcOf) htT hnc
  refine ⟨fun h => hxHV (h hxH), ?_, ?_⟩
  · exact (S.yOfL22_eq_commutator (inf_le_left.trans S.pCoreOf_mcOf_le) hx1 hx1V).symm
  · exact (S.yOfL22_eq_commutator (inf_le_left.trans hQT) hxH hxHV).symm

theorem stage1463_three_proof (h1413 : StageLemma1413) : Stage1463Three :=
  fun _ _ _ _ _ S _ hH _ hu => S.stage1463_three h1413 hH hu

end Three

end CFSG.Quasithin
