module

public import CFSG.Quasithin.Background.C48SporSetup

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

omit [Finite G] in
theorem isPGroup_ker_of_pow_mem {Y : Subgroup G} (hY : Y ≤ sporX H K)
    (hZ : IsPGroup 2 ↥(centerOf K)) (hpow : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ K) :
    IsPGroup 2 ↥(imgHom (N := sporN H K) hY).ker := by
  rintro ⟨y, hy⟩
  rw [mem_ker_imgHom_iff] at hy
  obtain ⟨e, he⟩ := hpow y y.2
  have hz : (y : G) ^ 2 ^ e ∈ centerOf K := ⟨he, Subgroup.pow_mem _ hy _⟩
  obtain ⟨f, hf⟩ := hZ ⟨_, hz⟩
  have hf' : (y : G) ^ 2 ^ (e + f) = 1 := by
    rw [pow_add, pow_mul]
    exact congrArg Subtype.val hf
  exact ⟨e + f, Subtype.ext (Subtype.ext (by simpa using hf'))⟩

theorem isPGroup_ker_M0 (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    IsPGroup 2 ↥(imgHom (N := sporN H K) (M0_le_sporX h h31)).ker :=
  isPGroup_ker_of_pow_mem _ h31.2.2 fun y hy => ⟨0, by simpa using h31.1 hy⟩

theorem M0R_le_sporX (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    conjClosure L M ⊔ R ≤ sporX H K :=
  sup_le (M0_le_sporX h h31) (R_le_sporX h h31)

theorem isPGroup_ker_M0R (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    IsPGroup 2 ↥(imgHom (N := sporN H K) (M0R_le_sporX h h31)).ker := by
  refine isPGroup_ker_of_pow_mem _ h31.2.2 fun y hy => ?_
  obtain ⟨e, he⟩ := InternalSec.two_of_sup h.pgroup
    (h.le_M.trans (le_normalizer_conjClosure L M)) y hy
  exact ⟨e, h31.1 he⟩

theorem img_V_le_center (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    img (sporN H K) V ≤ centerOf (pCoreOf 2 (img (sporN H K) (conjClosure L M) ⊔
      img (sporN H K) R)) := by
  rw [← img_sup (M0_le_sporX h h31) (R_le_sporX h h31),
    ← img_pCoreOf (M0R_le_sporX h h31) (isPGroup_ker_M0R h h31)]
  exact (img_mono h.V_center).trans img_centerOf_le

omit [Finite G] in
theorem M0_inf_centralizer_le (h31 : C31Basic H R M L V K) :
    conjClosure L M ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 (conjClosure L M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
  · intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have hmK : m ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer (h31.1 hm)
    constructor
    · rintro ⟨hc1, hc2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hm) c).mp hc1,
        conj_mem_centralizer hmK hc2⟩
    · rintro ⟨hc1, hc2⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hm) c).mpr hc1
      have h2 := conj_mem_centralizer (Subgroup.inv_mem _ hmK) hc2
      refine ⟨h1, ?_⟩
      have e : m⁻¹ * (m * c * m⁻¹) * m⁻¹⁻¹ = c := by group
      rwa [e] at h2
  · exact h31.2.2.to_le fun x hx => ⟨h31.1 hx.1, hx.2⟩

theorem img_centralizerSection (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    img (sporN H K) (centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M))) =
      centralizerSection (img (sporN H K) M) (img (sporN H K) (conjClosure L M))
        (pCoreOf 2 (img (sporN H K) (conjClosure L M))) := by
  rw [← img_pCoreOf (M0_le_sporX h h31) (isPGroup_ker_M0 h h31)]
  apply le_antisymm
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := mem_img.1 ha
    refine ⟨mk_mem_img hx.1,
      img_le_normalizer (Y := centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)))
        (Z := conjClosure L M) (fun _ hy => hy.2.1) ha,
      img_le_normalizer (Y := centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)))
        (Z := pCoreOf 2 (conjClosure L M)) (fun _ hy => hy.2.2.1) ha, fun b hb => ?_⟩
    obtain ⟨m, hm, rfl⟩ := mem_img.1 hb
    have := mk_mem_img (N := sporN H K) (x := m * x * m⁻¹ * x⁻¹) (hx.2.2.2 m hm)
    simpa using this
  · intro a ha
    obtain ⟨hMa, -, -, hca⟩ := ha
    obtain ⟨x, hxM, rfl⟩ := mem_img.1 hMa
    refine mk_mem_img ⟨hxM, le_normalizer_conjClosure L M hxM,
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
        (le_normalizer_conjClosure L M hxM), fun m hm => ?_⟩
    have hmX := M0_le_sporX h h31 hm
    have hc := hca _ (mk_mem_img (N := sporN H K) (x := ⟨m, hmX⟩) hm)
    set c : ↥(sporX H K) := ⟨m, hmX⟩ * x * ⟨m, hmX⟩⁻¹ * x⁻¹ with hcdef
    have hc' : (c : ↥(sporX H K) ⧸ sporN H K) ∈
        img (sporN H K) (pCoreOf 2 (conjClosure L M)) := by
      simpa [hcdef] using hc
    obtain ⟨o, ho, hoc⟩ := mem_img.1 hc'
    have hoc' : (o : G)⁻¹ * c ∈ Subgroup.centralizer (K : Set G) := by
      have := QuotientGroup.eq.mp hoc
      rw [mem_sporN] at this
      simpa using this
    have hcG : (c : G) = m * x * m⁻¹ * (x : G)⁻¹ := by simp [hcdef]
    have hcM0 : (c : G) ∈ conjClosure L M := by
      have hxm : (x : G) * m⁻¹ * (x : G)⁻¹ ∈ conjClosure L M :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure L M hxM) _).mp
          (Subgroup.inv_mem _ hm)
      have := Subgroup.mul_mem _ hm hxm
      rw [hcG]
      simpa [mul_assoc] using this
    have hoM0 : (o : G) ∈ conjClosure L M := CFSG.LieType.BorelTits.pCoreOf_le 2 _ ho
    have h1 : (o : G)⁻¹ * c ∈ pCoreOf 2 (conjClosure L M) :=
      M0_inf_centralizer_le h31
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hoM0) hcM0, hoc'⟩
    have := Subgroup.mul_mem _ ho h1
    rw [← hcG]
    simpa using this

theorem img_isSylowTwoOf (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    IsSylowTwoOf (img (sporN H K) R)
      (centralizerSection (img (sporN H K) M) (img (sporN H K) (conjClosure L M))
        (pCoreOf 2 (img (sporN H K) (conjClosure L M)))) := by
  rw [← img_centralizerSection h h31]
  have hC0 : centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)) ≤ M :=
    fun _ hx => hx.1
  exact isSylowTwoOf_img (hC0.trans (M_le_sporX h h31)) h.sylow

omit [Finite G] in
theorem le_center_or_eq_top_of_normal {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimp⟩ := hQ
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hNm : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    intro n hn
    have h1 : π n ∈ N.map π := Subgroup.mem_map_of_mem π hn
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff n).mp h1
  · right
    have hdec : ∀ g : Q, ∃ n ∈ N, ∃ z ∈ Subgroup.center Q, g = n * z := by
      intro g
      have hg : π g ∈ N.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp hg
      refine ⟨n, hn, n⁻¹ * g, ?_, by group⟩
      have : π (n⁻¹ * g) = 1 := by rw [map_mul, map_inv, hng, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    rw [eq_top_iff, ← hperf, _root_.commutator_def, Subgroup.commutator_le]
    intro g _ g' _
    obtain ⟨n, hn, z, hz, rfl⟩ := hdec g
    obtain ⟨n', hn', z', hz', rfl⟩ := hdec g'
    set ρ := QuotientGroup.mk' N with hρ
    have h1 : ρ ⁅n * z, n' * z'⁆ = 1 := by
      rw [map_commutatorElement, map_mul, map_mul,
        show ρ n = 1 from (QuotientGroup.eq_one_iff n).mpr hn,
        show ρ n' = 1 from (QuotientGroup.eq_one_iff n').mpr hn', one_mul, one_mul,
        commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul,
        (Subgroup.mem_center_iff.mp hz z').symm]
    exact (QuotientGroup.eq_one_iff _).mp h1

omit [Finite G] in
theorem commutator_sup_centerOf_left {W Y : Subgroup G} (hW : W ≤ K) (hY : Y ≤ K) :
    ⁅W ⊔ centerOf K, Y⁆ = ⁅W, Y⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg y hy
    have hZW : centerOf K ≤ Subgroup.normalizer (W : Set G) := fun z hz => by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      have hc : ∀ w ∈ K, z * w * z⁻¹ = w := fun w hw => by
        rw [(Subgroup.mem_centralizer_iff.mp hz.2 w hw).symm]
        group
      constructor
      · intro hw
        rwa [hc w (hW hw)]
      · intro hw
        have h1 := hc _ (hW hw)
        have hw' : w = z * w * z⁻¹ := by
          calc w = z⁻¹ * (z * w * z⁻¹) * z := by group
            _ = z⁻¹ * (z * (z * w * z⁻¹) * z⁻¹) * z := by rw [h1]
            _ = z * w * z⁻¹ := by group
        rwa [hw']
    obtain ⟨w, hw, z, hz, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hZW).1 hg
    have hzy : z * y = y * z := (Subgroup.mem_centralizer_iff.mp hz.2 y (hY hy)).symm
    have hzw : z * w = w * z := (Subgroup.mem_centralizer_iff.mp hz.2 w (hW hw)).symm
    have : ⁅w * z, y⁆ = ⁅w, y⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc w * z * y * (w * z)⁻¹ * y⁻¹ = w * (z * y) * z⁻¹ * w⁻¹ * y⁻¹ := by group
        _ = w * (y * z) * z⁻¹ * w⁻¹ * y⁻¹ := by rw [hzy]
        _ = w * y * w⁻¹ * y⁻¹ := by group
    rw [this]
    exact Subgroup.commutator_mem_commutator hw hy
  · exact Subgroup.commutator_mono le_sup_left le_rfl

omit [Finite G] in
theorem commutator_sup_centerOf {Y : Subgroup G} (hY : Y ≤ K) :
    ⁅Y ⊔ centerOf K, Y ⊔ centerOf K⁆ = ⁅Y, Y⁆ := by
  have hYZ : Y ⊔ centerOf K ≤ K := sup_le hY inf_le_left
  rw [commutator_sup_centerOf_left hY hYZ, Subgroup.commutator_comm,
    commutator_sup_centerOf_left hY hY]

omit [Finite G] in
theorem isSylowTwoOf_map_conj {S T : Subgroup G} (h : IsSylowTwoOf S T) (g : G) :
    IsSylowTwoOf (S.map (MulAut.conj g).toMonoidHom) (T.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hST, hS, hidx⟩ := h
  refine ⟨Subgroup.map_mono hST, hS.map _, ?_⟩
  have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) S T
    (MulEquiv.injective (MulAut.conj g))
  unfold Subgroup.relIndex at this
  rwa [this]

theorem mem_normalizer_of_map_le {S : Subgroup G} {x : G}
    (h : S.map (MulAut.conj x).toMonoidHom ≤ S) : x ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge h (le_of_eq ?_)
  exact (Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj x))).symm

omit [Finite G] in
theorem map_conj_le_sup_centerOf {Y : Subgroup G} (hYK : Y ≤ K) (hYX : Y ≤ sporX H K)
    {x : ↥(sporX H K)}
    (hx : (x : ↥(sporX H K) ⧸ sporN H K) ∈
      Subgroup.normalizer (img (sporN H K) Y : Set (↥(sporX H K) ⧸ sporN H K))) :
    Y.map (MulAut.conj (x : G)).toMonoidHom ≤ Y ⊔ centerOf K := by
  rintro _ ⟨y, hy, rfl⟩
  have hmk := (Subgroup.mem_normalizer_iff.mp hx _).mp
    (mk_mem_img (N := sporN H K) (x := ⟨y, hYX hy⟩) hy)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hmk
  obtain ⟨y', hy', hyy⟩ := mem_img.1 hmk
  have hc := QuotientGroup.eq.mp hyy
  rw [mem_sporN] at hc
  have hc' : (y' : G)⁻¹ * (x * y * (x : G)⁻¹) ∈ Subgroup.centralizer (K : Set G) := by
    simpa using hc
  have hxyK : (x : G) * y * (x : G)⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp x.2.2 y).mp (hYK hy)
  have hzK : (y' : G)⁻¹ * (x * y * (x : G)⁻¹) ∈ centerOf K :=
    ⟨K.mul_mem (K.inv_mem (hYK hy')) hxyK, hc'⟩
  have heq : (MulAut.conj (x : G)).toMonoidHom y = y' * ((y' : G)⁻¹ * (x * y * (x : G)⁻¹)) := by
    simp
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy') (Subgroup.mem_sup_right hzK)

theorem normalizer_inf_le_img_M (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    Subgroup.normalizer (img (sporN H K) V : Set (↥(sporX H K) ⧸ sporN H K)) ⊓
        Subgroup.normalizer (img (sporN H K) (conjClosure L M) :
          Set (↥(sporX H K) ⧸ sporN H K)) ≤ img (sporN H K) M := by
  rintro a ⟨haV, haM0⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  have hM0K := h31.1
  set f := (MulAut.conj (x : G)).toMonoidHom with hf
  have hM0 : (conjClosure L M).map f ≤ conjClosure L M := by
    have h1 := map_conj_le_sup_centerOf hM0K (M0_le_sporX h h31) haM0
    calc (conjClosure L M).map f
        = (⁅conjClosure L M, conjClosure L M⁆).map f := by
          rw [C2Nine.perfect_conjClosure_of_hyp h]
      _ = ⁅(conjClosure L M).map f, (conjClosure L M).map f⁆ := Subgroup.map_commutator _ _ _
      _ ≤ ⁅conjClosure L M ⊔ centerOf K, conjClosure L M ⊔ centerOf K⁆ :=
          Subgroup.commutator_mono h1 h1
      _ = conjClosure L M := by
          rw [commutator_sup_centerOf hM0K, C2Nine.perfect_conjClosure_of_hyp h]
  have hxM0 := mem_normalizer_of_map_le hM0
  have hM0eq : (conjClosure L M).map f = conjClosure L M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxM0
  have hV : V.map f ≤ V := by
    have h1 := map_conj_le_sup_centerOf (V_le_K h h31) (V_le_sporX h h31) haV
    calc V.map f = (⁅V, conjClosure L M⁆).map f := by rw [h.V_comm]
      _ = ⁅V.map f, (conjClosure L M).map f⁆ := Subgroup.map_commutator _ _ _
      _ ≤ ⁅V ⊔ centerOf K, conjClosure L M⁆ := by
          rw [hM0eq]
          exact Subgroup.commutator_mono h1 le_rfl
      _ = V := by rw [commutator_sup_centerOf_left (V_le_K h h31) hM0K, h.V_comm]
  have hxV := mem_normalizer_of_map_le hV
  exact mk_mem_img (h.V_norm ⟨x.2.1, hxV⟩)

theorem centralizer_le_centralizerSection (h : HypC28 H R M L V)
    (h31 : C31Basic H R M L V K) :
    Subgroup.centralizer (K : Set G) ⊓ sporX H K ≤
      centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)) := by
  rintro c ⟨hcK, hcX⟩
  have hc : ∀ y ∈ K, c * y * c⁻¹ = y := fun y hy => by
    rw [(Subgroup.mem_centralizer_iff.mp hcK y hy).symm]
    group
  have hnorm : ∀ {Y : Subgroup G}, Y ≤ K → c ∈ Subgroup.normalizer (Y : Set G) := fun {Y} hY => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rwa [hc y (hY hy)]
    · intro hy
      have h1 := hc _ (hY hy)
      have hy' : y = c * y * c⁻¹ := by
        calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
          _ = c⁻¹ * (c * (c * y * c⁻¹) * c⁻¹) * c := by rw [h1]
          _ = c * y * c⁻¹ := by group
      rwa [hy']
  refine ⟨mem_M_of_centralizer h h31 hcX.1 hcK, hnorm h31.1,
    hnorm ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans h31.1), fun y hy => ?_⟩
  have : y * c * y⁻¹ * c⁻¹ = 1 := by
    rw [Subgroup.mem_centralizer_iff.mp hcK y (h31.1 hy)]
    group
  rw [this]
  exact Subgroup.one_mem _

theorem normalizer_img_R_le (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    Subgroup.normalizer (img (sporN H K) R : Set (↥(sporX H K) ⧸ sporN H K)) ≤
      img (sporN H K) M := by
  intro a ha
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  set C' : Subgroup G := Subgroup.centralizer (K : Set G) ⊓ sporX H K with hC'
  set T : Subgroup G := R ⊔ C' with hT
  have hC'M : C' ≤ M := fun c hc => mem_M_of_centralizer h h31 hc.2.1 hc.1
  have hTM : T ≤ M := sup_le h.le_M hC'M
  have hTC0 : T ≤ centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)) :=
    sup_le h.sylow.1 (centralizer_le_centralizerSection h h31)
  have hRT : IsSylowTwoOf R T := by
    rw [A4.isSylowTwoOf_iff_maximal]
    exact ⟨le_sup_left, h.sylow.2.1, fun P hPT hP hRP =>
      ((A4.isSylowTwoOf_iff_maximal.mp h.sylow).2.2 P (hPT.trans hTC0) hP hRP)⟩
  set f := (MulAut.conj (x : G)).toMonoidHom with hf
  have hTmap : T.map f ≤ T := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      set r₀ : ↥(sporX H K) := ⟨r, R_le_sporX h h31 hr⟩ with hr₀
      have hmk := (Subgroup.mem_normalizer_iff.mp ha _).mp
        (mk_mem_img (N := sporN H K) (x := r₀) hr)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hmk
      obtain ⟨r', hr', hrr⟩ := mem_img.1 hmk
      have hc := QuotientGroup.eq.mp hrr
      rw [mem_sporN] at hc
      set c₀ : ↥(sporX H K) := r'⁻¹ * (x * r₀ * x⁻¹) with hc₀
      have heq : f r = (r' : G) * (c₀ : G) := by simp [hf, hc₀, hr₀]
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr')
        (Subgroup.mem_sup_right ⟨hc, c₀.2⟩)
    · rintro _ ⟨c, ⟨hcK, hcX⟩, rfl⟩
      refine Subgroup.mem_sup_right ⟨?_, ?_⟩
      · simpa [hf] using conj_mem_centralizer x.2.2 hcK
      · simpa [hf] using (sporX H K).mul_mem ((sporX H K).mul_mem x.2 hcX)
          ((sporX H K).inv_mem x.2)
  have hxT := mem_normalizer_of_map_le hTmap
  have hTeq : T.map f = T := Subgroup.mem_normalizer_iff_map_conj_eq.mp hxT
  have hRT' : IsSylowTwoOf (R.map f) T := by
    have := isSylowTwoOf_map_conj hRT (x : G)
    rwa [← hf, hTeq] at this
  obtain ⟨t, htT, hteq⟩ := IsSylowTwoOf.exists_conj hRT hRT'
  have hNR : t⁻¹ * (x : G) ∈ H ⊓ Subgroup.normalizer (R : Set G) := by
    refine ⟨H.mul_mem (H.inv_mem (h.le_H (hTM htT))) x.2.1,
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    have e : (MulAut.conj (t⁻¹ * (x : G))).toMonoidHom =
        (MulAut.conj t⁻¹).toMonoidHom.comp f := by
      ext g; simp [hf, mul_assoc]
    have e2 : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
      ext g; simp [mul_assoc]
    change R.map (MulAut.conj (t⁻¹ * (x : G))).toMonoidHom = R
    rw [e, ← Subgroup.map_map, hteq, Subgroup.map_map, e2, Subgroup.map_id]
  have hcgs : H ⊓ Subgroup.normalizer (R : Set G) ≤ cgsIn H R :=
    le_iSup_of_le R (le_iSup_of_le le_rfl (le_iSup_of_le (c2_9_two h).2.2.1
      (le_iSup_of_le (by rw [Subgroup.subgroupOf_self]; infer_instance) le_rfl)))
  have hxM : (x : G) ∈ M := by
    have := M.mul_mem (hTM htT) (h.cgs (hcgs hNR))
    simpa [mul_assoc] using this
  exact mk_mem_img hxM

theorem not_img_K_le (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K) : ¬ img (sporN H K) K ≤ img (sporN H K) M := by
  intro hle
  have hKX := K_le_sporX (H := H) hK.1
  have hKM : K ≤ M := by
    intro k hk
    obtain ⟨y, hyM, hyk⟩ := mem_img.1 (hle (mk_mem_img (N := sporN H K) (x := ⟨k, hKX hk⟩) hk))
    have hc := QuotientGroup.eq.mp hyk
    rw [mem_sporN] at hc
    have hcM : ((y⁻¹ * ⟨k, hKX hk⟩ : ↥(sporX H K)) : G) ∈ M :=
      mem_M_of_centralizer h h31 (y⁻¹ * (⟨k, hKX hk⟩ : ↥(sporX H K))).2.1 hc
    have := M.mul_mem hyM hcM
    simpa using this
  have hVbot : ∀ (hc : ∀ v ∈ V, ∀ m ∈ conjClosure L M, v * m = m * v), False := fun hc => by
    apply h.V_ne
    rw [← h.V_comm, eq_bot_iff, Subgroup.commutator_le]
    intro v hv m hm
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hc v hv m hm
  have hM0K := h31.1
  have hM0n : ((conjClosure L M).subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure L M (hKM g.2)) n).mp hn
  rcases le_center_or_eq_top_of_normal hK.2.2 hM0n with hc | ht
  · refine hVbot fun v hv m hm => ?_
    have := Subgroup.mem_center_iff.mp (hc (show (⟨m, hM0K hm⟩ : ↥K) ∈
      (conjClosure L M).subgroupOf K from hm)) ⟨v, V_le_K h h31 hv⟩
    exact congrArg Subtype.val this
  · have hKM0 : K ≤ conjClosure L M := fun k hk => by
      have : (⟨k, hk⟩ : ↥K) ∈ (conjClosure L M).subgroupOf K := by rw [ht]; trivial
      exact this
    have hVn : (V.subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using (Subgroup.mem_normalizer_iff.mp (M0_le_normalizer_V h (hKM0 g.2)) n).mp hn
    rcases le_center_or_eq_top_of_normal hK.2.2 hVn with hc | ht'
    · refine hVbot fun v hv m hm => ?_
      have := Subgroup.mem_center_iff.mp (hc (show (⟨v, V_le_K h h31 hv⟩ : ↥K) ∈
        V.subgroupOf K from hv)) ⟨m, hM0K hm⟩
      exact (congrArg Subtype.val this).symm
    ·
      have hKV : K ≤ V := fun k hk => by
        have : (⟨k, hk⟩ : ↥K) ∈ V.subgroupOf K := by rw [ht']; trivial
        exact this
      refine hVbot fun v hv m hm => ?_
      have := h.V_elem.1.is_comm.comm ⟨v, hv⟩ ⟨m, hKV (hM0K hm)⟩
      exact congrArg Subtype.val this

end CFSG.Quasithin.C48Spor
