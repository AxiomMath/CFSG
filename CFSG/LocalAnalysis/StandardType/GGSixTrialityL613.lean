module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613Defs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenTwelve
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section General

variable {G : Type} [Group G]

theorem eq_of_card_le_four_mul_of_commutator_eq [Finite G] {K Y : Subgroup G}
    (hK : ⁅K, K⁆ = K) (hYK : Y ≤ K) (hcard : Nat.card K ≤ 4 * Nat.card Y) : Y = K := by
  classical
  set I : Subgroup ↥K := Y.subgroupOf K with hI
  have hIc : Nat.card I = Nat.card Y := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv
  have hidx : Nat.card (↥K ⧸ I) ≤ 4 := by
    have h1 := I.card_mul_index
    rw [hIc, Subgroup.index_eq_card] at h1
    have hpos : 0 < Nat.card Y := Nat.card_pos
    by_contra h
    have h5 : Nat.card Y * 5 ≤ Nat.card Y * Nat.card (↥K ⧸ I) :=
      Nat.mul_le_mul_left _ (Nat.lt_of_not_le h)
    omega
  have : Group.IsSolvable (Equiv.Perm (↥K ⧸ I)) := Equiv.Perm.isSolvable hidx
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  set φ := MulAction.toPermHom ↥K (↥K ⧸ I) with hφ
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hsub : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  have hmem : ∀ k : ↥K, k ∈ I := by
    intro k
    have h1 : φ k = 1 := congrArg Subtype.val (Subsingleton.elim (⟨φ k, k, rfl⟩ : φ.range) 1)
    have h2 : k • ((1 : ↥K) : ↥K ⧸ I) = ((1 : ↥K) : ↥K ⧸ I) := by
      have := congrArg (fun σ : Equiv.Perm (↥K ⧸ I) => σ ((1 : ↥K) : ↥K ⧸ I)) h1
      simpa [hφ] using this
    rw [← MulAction.stabilizer_quotient I]
    exact h2
  have htop : I = ⊤ := eq_top_iff.mpr fun k _ => hmem k
  exact le_antisymm hYK (Subgroup.subgroupOf_eq_top.mp htop)

theorem exists_good_step_alperin [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (Good : G → Prop) {y g : G} (hy : y ∈ (S : Subgroup G)) (hg : g⁻¹ * y * g ∈ (S : Subgroup G))
    (hgood : Good (g⁻¹ * y * g)) (hbad : ¬ Good y) :
    ∃ Q : Subgroup G, CFSG.RankTwoShapes.IsAlperinSubgroup p (S : Subgroup G) Q ∧ ∃ z ∈ Q,
      ∃ n ∈ Subgroup.normalizer (Q : Set G), ¬ Good z ∧ Good (n⁻¹ * z * n) := by
  have hP : Subgroup.zpowers y ≤ (S : Subgroup G) := Subgroup.zpowers_le.2 hy
  have hPg : (Subgroup.zpowers y).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 (by simpa using hg)
  obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hP hPg
  have hcy : c⁻¹ * y * c = g⁻¹ * y * g := hcg y (Subgroup.mem_zpowers y)
  have key : ∀ c : G, CFSG.RankTwoShapes.AlperinDecomposition p (S : Subgroup G)
      (Subgroup.zpowers y) c → Good (c⁻¹ * y * c) →
      ∃ Q : Subgroup G, CFSG.RankTwoShapes.IsAlperinSubgroup p (S : Subgroup G) Q ∧ ∃ z ∈ Q,
        ∃ n ∈ Subgroup.normalizer (Q : Set G), ¬ Good z ∧ Good (n⁻¹ * z * n) := by
    intro c hc
    induction hc with
    | one =>
      intro h
      exact absurd (by simpa using h) hbad
    | @step c n Q _ hQ hyQ hn ih =>
      intro h
      by_cases hc' : Good (c⁻¹ * y * c)
      · exact ih hc'
      · refine ⟨Q, hQ, c⁻¹ * y * c, ?_, n, hn, hc', ?_⟩
        · exact hyQ ⟨y, Subgroup.mem_zpowers y, by simp⟩
        · have heq : (c * n)⁻¹ * y * (c * n) = n⁻¹ * (c⁻¹ * y * c) * n := by group
          rwa [heq] at h
  exact key c hc (hcy ▸ hgood)

theorem exists_conj_mem_center_of_pCentral [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (P : Sylow p G) (hPM : (P : Subgroup G) ≤ M) {d : G} (hd : GGPCentralIn p M d)
    (hdo : orderOf d = p) :
    ∃ m ∈ M, m * d * m⁻¹ ∈ (P : Subgroup G) ∧
      ∀ w ∈ (P : Subgroup G), w * (m * d * m⁻¹) = m * d * m⁻¹ * w := by
  classical
  set Cd : Subgroup M := (Subgroup.centralizer {d}).subgroupOf M with hCd
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p Cd))
  have hT' : IsPGroup p ((T : Subgroup Cd).map Cd.subtype) := T.isPGroup'.map _
  have hidx : ¬ p ∣ ((T : Subgroup Cd).map Cd.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h1 | h1
    · exact T.not_dvd_index h1
    · exact hd.2 h1
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (hT'.toSylow hidx) (P.subtype hPM)
  have hcomm : ∀ w ∈ (P : Subgroup G),
      w * ((m : G) * d * (m : G)⁻¹) = (m : G) * d * (m : G)⁻¹ * w := by
    intro w hw
    have hw' : (⟨w, hPM hw⟩ : M) ∈ ((m • hT'.toSylow hidx : Sylow p M) : Subgroup M) := by
      rw [hm, Sylow.coe_subtype, Subgroup.mem_subgroupOf]
      exact hw
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hw'
    obtain ⟨r, hr, hrw⟩ := hw'
    change r ∈ (T : Subgroup Cd).map Cd.subtype at hr
    obtain ⟨t, -, rfl⟩ := hr
    have htd : ((t : M) : G) * d = d * ((t : M) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp t.2)
    have hw2 : (m : G) * ((t : M) : G) * (m : G)⁻¹ = w := by
      have := congrArg Subtype.val hrw
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    rw [← hw2]
    calc (m : G) * ((t : M) : G) * (m : G)⁻¹ * ((m : G) * d * (m : G)⁻¹)
        = (m : G) * (((t : M) : G) * d) * (m : G)⁻¹ := by group
      _ = (m : G) * (d * ((t : M) : G)) * (m : G)⁻¹ := by rw [htd]
      _ = (m : G) * d * (m : G)⁻¹ * ((m : G) * ((t : M) : G) * (m : G)⁻¹) := by group
  refine ⟨m, m.2, ?_, hcomm⟩
  have hzo : orderOf ((m : G) * d * (m : G)⁻¹) = p := by
    have h := MulEquiv.orderOf_eq (MulAut.conj (m : G)) d
    rw [MulAut.conj_apply] at h
    rw [h, hdo]
  have hzp : IsPGroup p (Subgroup.zpowers ((m : G) * d * (m : G)⁻¹)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  have hzN : Subgroup.zpowers ((m : G) * d * (m : G)⁻¹) ≤
      Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    have hh : ∀ h' ∈ (P : Subgroup G), (m : G) * d * (m : G)⁻¹ * h' * ((m : G) * d * (m : G)⁻¹)⁻¹
        = h' := fun h' hh' => by rw [← hcomm h' hh']; group
    constructor
    · intro hP
      rw [hh h hP]
      exact hP
    · intro hP
      have h1 := hh _ hP
      set c := (m : G) * d * (m : G)⁻¹ with hc
      have h2 : h = c * h * c⁻¹ :=
        calc h = c⁻¹ * (c * h * c⁻¹) * c := by group
          _ = c⁻¹ * (c * (c * h * c⁻¹) * c⁻¹) * c := by rw [h1]
          _ = c * h * c⁻¹ := by group
      rw [h2]
      exact hP
  have hsup := P.is_maximal' (P.isPGroup'.to_sup_of_normal_left' hzp hzN) le_sup_left
  have hmem : (m : G) * d * (m : G)⁻¹ ∈ (P : Subgroup G) ⊔
      Subgroup.zpowers ((m : G) * d * (m : G)⁻¹) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  rwa [hsup] at hmem

theorem ggPCentralIn_of_sylow [Finite G] {p : ℕ} [Fact p.Prime] (M : Subgroup G) (P : Sylow p G)
    (hPM : (P : Subgroup G) ≤ M) {z : G} (hzP : z ∈ (P : Subgroup G))
    (hz : ∀ w ∈ (P : Subgroup G), w * z = z * w) : GGPCentralIn p M z := by
  refine ⟨hPM hzP, fun hdvd => ?_⟩
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer {z} := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hz w hw)
  have h1 : (Subgroup.centralizer {z}).relIndex M ∣ (P : Subgroup G).relIndex M :=
    Subgroup.relIndex_dvd_of_le_left M hPC
  have h2 := Subgroup.relIndex_mul_index hPM
  exact P.not_dvd_index (h2 ▸ dvd_mul_of_dvd_left (hdvd.trans h1) _)

end General

section Layer

variable {G : Type} [Group G]

theorem ggPsiInnerDiag_of_mem_range {U : Type*} [Group U] (Δ : UniversalRootDatum U)
    {ψ : U →* G} {c : G} (hc : c ∈ ψ.range) : GGPsiInnerDiag Δ ψ c :=
  ⟨c⁻¹, ψ.range.inv_mem hc, fun _ _ => ⟨1, Subgroup.one_mem _, fun z _ => by simp⟩⟩

theorem conj_mem_of_layer_le [Finite G] {M G₀ : Subgroup G} {z k : G} {f : ℕ}
    (hCz : Subgroup.centralizer {z} ≤ M)
    (hzK : z ∈ LargeEvenLayer (M ⊓ Subgroup.centralizer {z}))
    (hperf : ∀ X : Subgroup G, X ≤ M ⊓ Subgroup.centralizer {z} → ⁅X, X⁆ = X →
      X ≤ LargeEvenLayer (M ⊓ Subgroup.centralizer {z}))
    (hcard : ∀ (H : Type) [Group H], LieModel H .PSL 3 2 f →
      Nat.card ↥(LargeEvenLayer (M ⊓ Subgroup.centralizer {z})) ≤ 3 * Nat.card H)
    (hlie : LieModel (↥(LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {k⁻¹ * z * k})) ⧸
      Subgroup.center ↥(LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {k⁻¹ * z * k}))) .PSL 3 2 f) :
    k⁻¹ * z * k ∈ G₀ := by
  set y := k⁻¹ * z * k with hy
  set X := LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {y}) with hX
  set K := LargeEvenLayer (M ⊓ Subgroup.centralizer {z}) with hK
  set Y := X.map (MulAut.conj k).toMonoidHom with hYdef
  have hXle : X ≤ G₀ ⊓ Subgroup.centralizer {y} := LayerCC.largeEvenLayer_le _
  have hzy : z = k * y * k⁻¹ := by rw [hy]; group
  have hYC : Y ≤ Subgroup.centralizer {z} := by
    rintro _ ⟨w, hw, rfl⟩
    have hwy : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.mp (hXle hw).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hzy]
    calc k * w * k⁻¹ * (k * y * k⁻¹) = k * (w * y) * k⁻¹ := by group
      _ = k * (y * w) * k⁻¹ := by rw [hwy]
      _ = k * y * k⁻¹ * (k * w * k⁻¹) := by group
  have hYM : Y ≤ M ⊓ Subgroup.centralizer {z} := le_inf (hYC.trans hCz) hYC
  have hXp : ⁅X, X⁆ = X := LayerCC.commutator_largeEvenLayer _
  have hYp : ⁅Y, Y⁆ = Y := by rw [hYdef, ← Subgroup.map_commutator, hXp]
  have hYK : Y ≤ K := hperf Y hYM hYp
  have hKp : ⁅K, K⁆ = K := LayerCC.commutator_largeEvenLayer _
  have hcardY : Nat.card Y = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hq : Nat.card (↥X ⧸ Subgroup.center ↥X) ≤ Nat.card X :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hKc := hcard _ hlie
  have hYeq : Y = K := eq_of_card_le_four_mul_of_commutator_eq hKp hYK (by omega)
  have hzY : z ∈ Y := hYeq ▸ hzK
  obtain ⟨w, hw, hwz⟩ := hzY
  have hwy : w = y := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwz
    rw [hy, ← hwz]
    group
  rw [← hwy]
  exact (hXle hw).1

end Layer

section Inputs

theorem ggSixLSixElevenV2Input_of_input (h : GGSixLSixElevenInput) : GGSixLSixElevenV2Input :=
  fun G _ _ p B Bs x L D J t n f ψ hctx hC hU _ b hb hCb g hg hgM =>
    h G p B Bs x L D J t n f ψ hctx hC hU b hb hCb g hg hgM

theorem ggSixTrialityInput_of_central (h611 : GGSixLSixElevenV2Input)
    (hKG : GGD4TrialityCentralInput) (hD : GGSixTrialityDCentralInput) :
    GGSixTrialityInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC hU h9 b hb hCb g hg htri
  by_contra hgM
  have htri' := htri
  obtain ⟨-, -, hp3, -, -, -⟩ := htri
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := hctx.fusionSetting hC hU
  set M := ggM 3 B x L D J with hM
  have hb1 : b ≠ 1 := ne_one_of_centralizer_le hCb hgM
  have hyo : orderOf (g⁻¹ * b * g) = 3 := hS.orderOf_conj hb hb1 g
  obtain ⟨P, hBsP, hPM, -⟩ := hS.exists_sylow
  obtain ⟨g', hg'P, hg'M⟩ := hS.exists_conj_mem_sylow P hPM hb hb1 hg hgM
  set Good : G → Prop := fun w => ∃ m ∈ M, m⁻¹ * w * m ∈ Bs with hGood
  have hbad : ¬ Good (g'⁻¹ * b * g') := fun ⟨m, hm, hmem⟩ =>
    hS.not_conj_mem hb hCb hg'M m hm hmem
  have hbb : (g'⁻¹)⁻¹ * (g'⁻¹ * b * g') * g'⁻¹ = b := by group
  have hgoodb : Good ((g'⁻¹)⁻¹ * (g'⁻¹ * b * g') * g'⁻¹) :=
    ⟨1, M.one_mem, by rw [hbb]; simpa using hb⟩
  obtain ⟨Q, hQ, z₀, -, k, hk, hz₀bad, hkgood⟩ :=
    exists_good_step_alperin P Good hg'P (by rw [hbb]; exact hBsP hb) hgoodb hbad
  have hkM : k ∉ M := by
    intro hkM
    obtain ⟨m, hm, hmem⟩ := hkgood
    refine hz₀bad ⟨k * m, M.mul_mem hkM hm, ?_⟩
    have heq : (k * m)⁻¹ * z₀ * (k * m) = m⁻¹ * (k⁻¹ * z₀ * k) * m := by group
    rw [heq]
    exact hmem
  obtain ⟨d, hdD, hd1, hdcen⟩ := hD G 3 B Bs x L D J t n f ψ hctx hC (g⁻¹ * b * g) hg hyo htri'
  have hdo : orderOf d = 3 := orderOf_eq_prime (hctx.d_elem.2 d hdD) hd1
  obtain ⟨m, hm, hzP, hzc⟩ := exists_conj_mem_center_of_pCentral P hPM hdcen hdo
  set z := m * d * m⁻¹ with hz
  have hzo : orderOf z = 3 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj m) d
    rw [MulAut.conj_apply] at h
    rw [hz, h, hdo]
  have hzQ : z ∈ Q :=
    hQ.2.2.1 ⟨Subgroup.mem_centralizer_iff.mpr fun w hw => hzc w (hQ.1 hw), hzP⟩
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hzBs : z ∈ Bs :=
    hS.omega z (Subgroup.mem_centralizer_iff.mpr fun w hw => hzc w (hBsP hw)) hz3
  have hzcen : GGPCentralIn 3 M z := ggPCentralIn_of_sylow M P hPM hzP hzc
  have hCz : Subgroup.centralizer {z} ≤ M := by
    intro w hw
    have hw' : m⁻¹ * w * m ∈ Subgroup.centralizer {d} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
      have hd : d = m⁻¹ * z * m := by rw [hz]; group
      rw [hd]
      calc m⁻¹ * w * m * (m⁻¹ * z * m) = m⁻¹ * (w * z) * m := by group
        _ = m⁻¹ * (z * w) * m := by rw [hw]
        _ = m⁻¹ * z * m * (m⁻¹ * w * m) := by group
    have hwm := M.mul_mem (M.mul_mem hm (h9 d hdD hd1 hw')) (M.inv_mem hm)
    have heq : m * (m⁻¹ * w * m) * m⁻¹ = w := by group
    rwa [heq] at hwm
  obtain ⟨hzK, hperf, hcard⟩ :=
    hKG G (ggG0 3 B x L D J) t n f ψ hctx.presents hC (g⁻¹ * b * g) hg hyo htri' z hzo hzcen
  have hkz : k⁻¹ * z * k ∈ M := hPM (hQ.1 (conj_inv_mem_of_mem_normalizer hk hzQ))
  rcases h611 G 3 B Bs x L D J t n f ψ hctx hC hU h9 z hzBs hCz k hkz hkM with hlin | htz
  · exact absurd hlin.1 (by norm_num)
  · obtain ⟨-, -, -, -, hninner, hlie⟩ := htz
    refine hninner (ggPsiInnerDiag_of_mem_range _ ?_)
    rw [hctx.range_eq]
    exact conj_mem_of_layer_le hCz hzK hperf hcard hlie

theorem ggSixTrialityInput_of_lSixEleven_central (h611 : GGSixLSixElevenInput)
    (hKG : GGD4TrialityCentralInput) (hD : GGSixTrialityDCentralInput) :
    GGSixTrialityInput :=
  ggSixTrialityInput_of_central (ggSixLSixElevenV2Input_of_input h611) hKG hD

end Inputs

end CFSG.StandardType
