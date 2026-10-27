module

public import CFSG.Quasithin.H13.L32ARuOne
public import CFSG.Quasithin.H13.L32ASigma
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits
open scoped IsMulCommutative

namespace L32A

variable {G : Type} [Group G]

theorem center_perm_fin_five_eq_bot : Subgroup.center (Equiv.Perm (Fin 5)) = ⊥ := by
  have key : ∀ g : Equiv.Perm (Fin 5), g * Equiv.swap 0 1 = Equiv.swap 0 1 * g →
      g * (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) =
        (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) * g → g = 1 := by
    decide +kernel
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_center_iff] at hg
  rw [Subgroup.mem_bot]
  exact key g (hg _).symm (hg _).symm

theorem card_SL_two_F4 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) RuType.F4) = 60 := by
  rw [Matrix.card_SL_field, RuType.F4.card]
  norm_num [Fin.prod_univ_two]

theorem normalizer_eq_centralizer_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) :
    Subgroup.normalizer (A : Set G) = Subgroup.centralizer (A : Set G) := by
  refine le_antisymm ?_ (Subgroup.centralizer_le_normalizer _)
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  · have hga : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
    have hga1 : g * a * g⁻¹ ≠ 1 := fun h1 => ha1 (by
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group)
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).mp hA
    have e1 : (⟨g * a * g⁻¹, hga⟩ : ↥A) = y :=
      hy _ fun h => hga1 (congrArg Subtype.val h)
    have e2 : (⟨a, ha⟩ : ↥A) = y := hy _ fun h => ha1 (congrArg Subtype.val h)
    have e : g * a * g⁻¹ = a := congrArg Subtype.val (e1.trans e2.symm)
    calc a * g = g * a * g⁻¹ * g := by rw [e]
      _ = g * a := by group

theorem pCoreOf_le_of_sylow [Finite G] {L T : Subgroup G} (hTp : IsPGroup 2 T) (hTL : T ≤ L)
    (hidx : ¬ 2 ∣ (T.subgroupOf L).index) : pCoreOf 2 L ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTpL : IsPGroup 2 (T.subgroupOf L) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  let S : Sylow 2 L := hTpL.toSylow hidx
  have hcore : CFSG.Open.pCore 2 L ≤ (S : Subgroup L) := by
    have := CFSG.LieType.BorelTits.pCore_normal (G := L) 2
    exact (CFSG.LieType.BorelTits.pCore_isPGroup (G := L) 2).le_sylow_of_normal S
  rintro x ⟨y, hy, rfl⟩
  have h2 := hcore hy
  have hS : (S : Subgroup L) = T.subgroupOf L := rfl
  rw [hS] at h2
  exact h2

theorem sq_eq_one_of_mem_conjClosure {V H : Subgroup G} (hV : ∀ v ∈ V, v ^ 2 = 1)
    (hcomm : ∀ x ∈ conjClosure V H, ∀ y ∈ conjClosure V H, x * y = y * x) :
    ∀ u ∈ conjClosure V H, u ^ 2 = 1 := by
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, -, v, hv, rfl⟩ := hx
    rw [conj_pow, hV v hv]
    group
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy := hcomm x hx y hy
    calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
      _ = x * (x * y) * y := by rw [← hxy]
      _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x _ ih => rw [inv_pow, ih, inv_one]


theorem centerOf_eq_fsuV1 (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule)
    (h72 : Lemma14_7_72) (h74 : Lemma14_7_74) {G : Type} [Group G] [Finite G]
    {T L V : Subgroup G} (h : Hyp147 G T L V) : centerOf T = fsuV1 T V := by
  obtain ⟨hS, -, -, -, hVZ, -, -⟩ := h72 G T L V h
  obtain ⟨⟨hML, -⟩, -⟩ := h74 G T L V h
  obtain ⟨hVel, -, -, -, -, -⟩ := hMod G T L V h.hyp h.fsu
  have hTL : T ≤ L := (h.normalizes h13322).trans hML.le
  have hT := h.fsu.sylow
  have hidx : ¬ 2 ∣ (T.subgroupOf L).index := by
    intro hd
    apply hT.2
    rw [← Subgroup.relIndex_mul_index hTL]
    exact Dvd.dvd.mul_right hd _
  have hSle : pCoreOf 2 L ≤ T := pCoreOf_le_of_sylow hT.1 hTL hidx
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxCS : x ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) :=
      Subgroup.centralizer_le hSle hxC
    have hF : quasithinGenFitting L = pCoreOf 2 L := h.fsu.faithful.2.2.1
    have hxS : x ∈ pCoreOf 2 L := by
      have := centralizer_quasithinGenFitting_le L
        (Subgroup.mem_inf.mpr ⟨hTL hxT, by rw [hF]; exact hxCS⟩)
      rwa [hF] at this
    have hxV : x ∈ V := by
      rw [hVZ, hS]
      exact Subgroup.mem_inf.mpr ⟨hxS, hxCS⟩
    exact Subgroup.mem_inf.mpr ⟨hxV, Subgroup.subset_closure
      ⟨Subgroup.mem_inf.mpr ⟨hxT, hxC⟩, hVel.2 x hxV⟩⟩
  · intro x hx
    exact ((Subgroup.closure_le _).mpr fun z hz => hz.1) (Subgroup.mem_inf.mp hx).2

theorem ruTwo_of_inputs (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) (h72 : Lemma14_7_72) (h73 : Lemma14_7_73) (h74 : Lemma14_7_74)
    {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (h : Hyp147 G T L V)
    (T' : Sylow 2 G) (hT' : (T' : Subgroup G) = T) : RuType.RuTwo L T' := by
  obtain ⟨hHz, -, hHKT, -, hS5, -, U₀, hU₀, hL24⟩ := h63 G T L V h
  obtain ⟨hS, -, -, hU0V1, hVZ, -, -⟩ := h72 G T L V h
  obtain ⟨-, -, h73k⟩ := h73 G T L V h
  obtain ⟨⟨hML, -⟩, -, hQ⟩ := h74 G T L V h
  obtain ⟨hVel, -, -, hV1, -, -⟩ := hMod G T L V h.hyp h.fsu
  have hTL : T ≤ L := (h.normalizes h13322).trans hML.le
  have hT := h.fsu.sylow
  have hidxTL : ¬ 2 ∣ (T.subgroupOf L).index := by
    intro hd
    apply hT.2
    rw [← Subgroup.relIndex_mul_index hTL]
    exact Dvd.dvd.mul_right hd _
  have hZT := centerOf_eq_fsuV1 h13322 hMod h72 h74 h
  have hcore : centerOf (pCoreOf 2 L) = V := by rw [← hS, ← hVZ]
  have hNC := normalizer_eq_centralizer_of_card_two hV1
  have hUeq : conjClosure V (Subgroup.centralizer (fsuV1 T V : Set G)) = fsuU T V := by
    rw [← hNC]
  have hUab := h.abelian
  have hUcomm : ∀ x ∈ fsuU T V, ∀ y ∈ fsuU T V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(fsuU T V)) ⟨y, hy⟩)
  have hUel : ∀ u ∈ fsuU T V, u ^ 2 = 1 :=
    sq_eq_one_of_mem_conjClosure (fun v hv => hVel.2 v hv) hUcomm
  have hU0 : U₀ = fsuV1 T V := by
    ext u
    rw [hU₀]
    constructor
    · rintro ⟨huU, hk⟩
      exact hU0V1 u huU hk
    · intro hu
      refine ⟨le_conjClosure V _ (Subgroup.mem_inf.mp hu).1, fun k hk => ?_⟩
      have hkH : k ∈ L32A.hz T V := oTwoUpper_le _ hk
      have hc := Subgroup.mem_centralizer_iff.mp hkH u hu
      rw [← hc, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  obtain ⟨k, hkK, hkM⟩ : ∃ k ∈ L32A.kz T V, k ∉ L32A.m1 T L V := by
    by_contra hcon
    apply hHz.2.1
    rw [hHKT]
    refine sup_le (fun k hk => ?_) (h.normalizes h13322)
    by_contra hk'
    exact hcon ⟨k, hk, fun hm => hk' (Subgroup.mem_inf.mp hm).2⟩
  obtain ⟨-, -, -, -, hEl, hidx6, hindec, -, -, -, -⟩ := h73k k hkK hkM
  obtain ⟨hKN, π, β, hπs, hπker, hβs, hβker, hint⟩ := hL24
  obtain ⟨ρ, hρs, hρker⟩ := hS5
  have hKH : L32A.kz T V ≤ L32A.hz T V := oTwoUpper_le _
  have hQK : pCoreOf 2 (L32A.hz T V) ≤ L32A.kz T V := hQ ▸ Subgroup.map_subtype_le _
  have hcardQ : Nat.card ↥(pCoreOf 2 (L32A.hz T V)) =
      Nat.card ↥(CFSG.Open.pCore 2 ↥(L32A.hz T V)) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hcardH : Nat.card ↥(L32A.hz T V) = 120 * Nat.card ↥(pCoreOf 2 (L32A.hz T V)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv, Nat.card_perm,
      Nat.card_fin, hρker] at h1
    rw [h1, hcardQ]
    rfl
  have hcardK : Nat.card ↥(L32A.kz T V) = 60 * Nat.card ↥(pCoreOf 2 (L32A.hz T V)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    have hc : Nat.card ↥((pCoreOf 2 (L32A.kz T V)).subgroupOf (L32A.kz T V)) =
        Nat.card ↥(pCoreOf 2 (L32A.kz T V)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (L32A.kz T V))).toEquiv
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv,
      card_SL_two_F4, hπker, hc, ← hQ] at h1
    exact h1
  have hidx2 : ((L32A.kz T V).subgroupOf (L32A.hz T V)).index = 2 := by
    have h1 := Subgroup.card_mul_index ((L32A.kz T V).subgroupOf (L32A.hz T V))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv, hcardK, hcardH] at h1
    have hpos : 0 < Nat.card ↥(pCoreOf 2 (L32A.hz T V)) := Nat.card_pos
    have h2 : 60 * Nat.card ↥(pCoreOf 2 (L32A.hz T V)) *
        ((L32A.kz T V).subgroupOf (L32A.hz T V)).index =
          60 * Nat.card ↥(pCoreOf 2 (L32A.hz T V)) * 2 := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have ht : ∃ t ∈ L32A.hz T V, t ∉ L32A.kz T V := by
    by_contra hcon
    have htop : (L32A.kz T V).subgroupOf (L32A.hz T V) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_subgroupOf]
      by_contra hx
      exact hcon ⟨x, x.2, hx⟩
    rw [htop, Subgroup.index_top] at hidx2
    norm_num at hidx2
  have hidx : ∀ a ∈ L32A.hz T V, ∀ b ∈ L32A.hz T V, a ∉ L32A.kz T V → b ∉ L32A.kz T V →
      a * b⁻¹ ∈ L32A.kz T V := by
    intro a ha b hb haK hbK
    have hmem := (Subgroup.mul_mem_iff_of_index_two hidx2 (a := ⟨a, ha⟩)
      (b := (⟨b, hb⟩ : ↥(L32A.hz T V))⁻¹)).mpr (iff_of_false
        (fun h' => haK (Subgroup.mem_subgroupOf.mp h'))
        (fun h' => hbK (by
          have h'' := Subgroup.mem_subgroupOf.mp h'
          simpa using h'')))
    simpa [Subgroup.mem_subgroupOf] using hmem
  have hZ : ∀ a ∈ L32A.hz T V,
      (∀ b ∈ L32A.hz T V, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 (L32A.hz T V)) →
        a ∈ pCoreOf 2 (L32A.hz T V) := by
    intro a ha hab
    have hcent : ρ ⟨a, ha⟩ ∈ Subgroup.center (Equiv.Perm (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨b, rfl⟩ := hρs g
      have hmem : (⟨a, ha⟩ : ↥(L32A.hz T V)) * b * (⟨a, ha⟩ : ↥(L32A.hz T V))⁻¹ * b⁻¹ ∈
          ρ.ker := by
        rw [hρker]
        obtain ⟨y, hy, hye⟩ := hab b b.2
        have hy' : y = (⟨a, ha⟩ : ↥(L32A.hz T V)) * b * (⟨a, ha⟩ : ↥(L32A.hz T V))⁻¹ * b⁻¹ :=
          Subtype.ext (by simpa using hye)
        rw [← hy']
        exact hy
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hmem
      calc ρ b * ρ ⟨a, ha⟩ =
          (ρ ⟨a, ha⟩ * ρ b * (ρ ⟨a, ha⟩)⁻¹ * (ρ b)⁻¹)⁻¹ * (ρ ⟨a, ha⟩ * ρ b) := by group
        _ = ρ ⟨a, ha⟩ * ρ b := by rw [hmem, inv_one, one_mul]
    rw [center_perm_fin_five_eq_bot, Subgroup.mem_bot] at hcent
    have hker : (⟨a, ha⟩ : ↥(L32A.hz T V)) ∈ ρ.ker := hcent
    rw [hρker] at hker
    exact ⟨_, hker, rfl⟩
  let D : NatSL24 (L32A.hz T V) (L32A.kz T V) (pCoreOf 2 (L32A.hz T V)) (fsuU T V)
      (fsuV1 T V) :=
    { π := π
      β := β
      K_le := hKH
      conj_K := fun a ha k hk => conj_mem_oTwoUpper (Subgroup.le_normalizer ha) hk
      conj_U := fun a ha u hu => by
        have ha' : a ∈ Subgroup.normalizer (fsuV1 T V : Set G) := by rw [hNC]; exact ha
        exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V _ ha') u).mp hu
      conj_Z := fun a ha z hz => by
        have hc := Subgroup.mem_centralizer_iff.mp ha z hz
        rw [← hc, mul_inv_cancel_right]
        exact hz
      π_surj := hπs
      π_ker := by rw [hπker, hQ]
      β_surj := hβs
      β_ker := by rw [hβker, hU0]
      β_conj := hint }
  obtain ⟨φ, ψ, hφs, hφker, hψs, hψker, hψint⟩ := D.exists_sigma hQK ht hidx hZ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hT', inf_eq_left.mpr hTL]
    exact hidxTL
  ·
    rw [hT', hZT, hcore]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := hVel.1
    exact congrArg Subtype.val (mul_comm (⟨z, (Subgroup.mem_inf.mp hz).1⟩ : ↥V) ⟨v, hv⟩)
  ·
    rw [hT', hZT, hcore]
    exact (inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V _)
  ·
    rw [hT', hZT, hcore, hUeq, hQ]
    exact hEl.1
  ·
    rw [hT', hZT]
    exact ⟨ρ, hρs, hρker.trans (Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _) _).symm⟩
  ·
    rw [hT', hZT, hcore, hUeq]
    intro u hu u' hu'
    refine ⟨?_, ?_⟩
    · rw [hUcomm u hu u' hu', mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · rw [hUel u hu]
      exact one_mem _
  ·
    rw [hT', hZT, hcore, hUeq, hQ]
    intro q hq u hu
    have hqK : q ∈ L32A.kz T V := Subgroup.map_subtype_le _ hq
    have hπq : π ⟨q, hqK⟩ = 1 := by
      have hmem : (⟨q, hqK⟩ : ↥(L32A.kz T V)) ∈ π.ker := by
        rw [hπker, Subgroup.mem_subgroupOf]
        exact hq
      exact hmem
    have hqu : q * u * q⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (hKN hqK) u).mp hu
    have h1 := hint ⟨q, hqK⟩ ⟨u, hu⟩ ⟨q * u * q⁻¹, hqu⟩ rfl
    rw [hπq, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, ofAdd_toAdd] at h1
    have h2 : (⟨q * u * q⁻¹, hqu⟩ : ↥(fsuU T V)) * (⟨u, hu⟩ : ↥(fsuU T V))⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    rw [hβker, hU0, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  ·
    rw [hT', hZT, hcore, hUeq]
    exact ⟨φ, ψ, hφs, hφker, hψs, hψker, hψint⟩
  ·
    rw [hT', hZT, hcore, hUeq, hQ]
    exact hEl.2
  ·
    rw [hT', hZT, hcore, hUeq, hQ]
    exact hidx6
  ·
    rw [hT', hZT, hcore, hUeq, hQ]
    intro A B hUA hUB hAQ hBQ hHA hHB hAB hAB'
    exact hindec A B hUA hUB hAQ hBQ (hKH.trans hHA) (hKH.trans hHB) hAB hAB'

end L32A

end CFSG.Quasithin.H13
