module

public import CFSG.Quasithin.MS93.ASGroup
public import CFSG.Quasithin.Background.C48SporCase

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem blockQ_le_sporX (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    blockQ (conjClosure L M) ≤ sporX H K :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (M0_le_sporX h h31)

omit [Finite G] in
theorem blockU_le_M0 (L₀ : Subgroup G) : blockU L₀ ≤ L₀ :=
  commutator_le_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 _) le_rfl

theorem blockU_le_sporX (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    blockU (conjClosure L M) ≤ sporX H K :=
  (blockU_le_M0 _).trans (M0_le_sporX h h31)

theorem blockZ_le_sporX (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    blockZ (conjClosure L M) ≤ sporX H K :=
  inf_le_left.trans (blockU_le_sporX h h31)

theorem blockQ_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    blockQ (img (sporN H K) (conjClosure L M)) = img (sporN H K) (blockQ (conjClosure L M)) :=
  (img_pCoreOf (M0_le_sporX h h31) (isPGroup_ker_M0 h h31)).symm

theorem blockU_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    blockU (img (sporN H K) (conjClosure L M)) = img (sporN H K) (blockU (conjClosure L M)) := by
  unfold blockU
  rw [blockQ_img h h31, img_commutator (blockQ_le_sporX h h31) (M0_le_sporX h h31)]

theorem le_normalizer_blockZ' {Y : Type} [Group Y] (L₀ : Subgroup Y) :
    L₀ ≤ Subgroup.normalizer (blockZ L₀ : Set Y) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨u, ⟨huU, huC⟩, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_commutator_right' _ _ hl) u).mp huU,
      ?_⟩
    simpa using conj_mem_centralizer (Subgroup.le_normalizer hl) huC
  · intro u ⟨huU, huC⟩
    refine ⟨l⁻¹ * u * l, ⟨?_, ?_⟩, by simp [mul_assoc]⟩
    · have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_commutator_right' _ _ (L₀.inv_mem hl)) u).mp huU
      show l⁻¹ * u * l ∈ ⁅blockQ L₀, L₀⁆
      simpa using this
    · have := conj_mem_centralizer (Subgroup.le_normalizer (L₀.inv_mem hl)) huC
      simpa using this

theorem blockZ_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    blockZ (img (sporN H K) (conjClosure L M)) = img (sporN H K) (blockZ (conjClosure L M)) := by
  unfold blockZ
  rw [blockU_img h h31]
  apply le_antisymm
  · rintro a ⟨haU, haC⟩
    obtain ⟨u, huU, rfl⟩ := mem_img.1 haU
    have huK : (u : G) ∈ K := h31.1 (blockU_le_M0 _ huU)
    exact mk_mem_img ⟨huU, (mk_mem_centralizer_iff h h31 huK).1 haC⟩
  · intro a ha
    obtain ⟨u, ⟨huU, huC⟩, rfl⟩ := mem_img.1 ha
    have huK : (u : G) ∈ K := h31.1 (blockU_le_M0 _ huU)
    exact ⟨mk_mem_img huU, (mk_mem_centralizer_iff h h31 huK).2 huC⟩

theorem V_le_blockQ (h : HypC28 H R M L V) : V ≤ blockQ (conjClosure L M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.V_le (M0_le_normalizer_V h) ?_
  intro v
  exact ⟨1, Subtype.ext (by simpa using h.V_elem.2 v v.2)⟩

theorem V_le_blockU (h : HypC28 H R M L V) : V ≤ blockU (conjClosure L M) := by
  rw [← h.V_comm]
  exact Subgroup.commutator_mono (V_le_blockQ h) le_rfl

theorem mem_blockZ_of_mk (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    {u : ↥(sporX H K)} (huU : (u : G) ∈ blockU (conjClosure L M))
    (hu : (u : ↥(sporX H K) ⧸ sporN H K) ∈ blockZ (img (sporN H K) (conjClosure L M))) :
    (u : G) ∈ blockZ (conjClosure L M) := by
  rw [blockZ_img h h31] at hu
  obtain ⟨z, ⟨hzU, hzC⟩, hzu⟩ := mem_img.1 hu
  have hc := QuotientGroup.eq.mp hzu
  rw [mem_sporN] at hc
  have hc' : (z : G)⁻¹ * u ∈ Subgroup.centralizer (K : Set G) := by simpa using hc
  have hcL : (z : G)⁻¹ * u ∈ Subgroup.centralizer (conjClosure L M : Set G) :=
    Subgroup.centralizer_le h31.1 hc'
  have := Subgroup.mul_mem _ hzC hcL
  refine ⟨huU, ?_⟩
  simpa using this

omit [Finite G] in
theorem commutator_sup_le_of_centralizes {W Y Z' : Subgroup G}
    (hW : Z' ≤ Subgroup.centralizer (W : Set G)) (hY : Z' ≤ Subgroup.centralizer (Y : Set G)) :
    ⁅W ⊔ Z', Y⁆ ≤ ⁅W, Y⁆ := by
  rw [Subgroup.commutator_le]
  intro g hg y hy
  obtain ⟨w, hw, z, hz, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer
    (hW.trans (Subgroup.centralizer_le_normalizer _))).1 hg
  have hzy : z * y = y * z := (Subgroup.mem_centralizer_iff.mp (hY hz) y hy).symm
  have : ⁅w * z, y⁆ = ⁅w, y⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc w * z * y * (w * z)⁻¹ * y⁻¹ = w * (z * y) * z⁻¹ * w⁻¹ * y⁻¹ := by group
      _ = w * (y * z) * z⁻¹ * w⁻¹ * y⁻¹ := by rw [hzy]
      _ = w * y * w⁻¹ * y⁻¹ := by group
  rw [this]
  exact Subgroup.commutator_mem_commutator hw hy

omit [Finite G] in
theorem eq_top_of_isPGroup_quotient {Y : Type*} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (N' : Subgroup Y) [N'.Normal] (hp : IsPGroup 2 (Y ⧸ N')) : N' = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf' : commutator (Y ⧸ N') = ⊤ := by
    rw [_root_.commutator_def, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N'),
      ← Subgroup.map_commutator, ← _root_.commutator_def, hperf]
  have hlcs : ∀ n, (⊤ : Subgroup (Y ⧸ N')).lowerCentralSeries n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Subgroup.lowerCentralSeries_succ, ih, ← _root_.commutator_def, hperf']
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hp.isNilpotent
  rw [hlcs] at hn
  rw [eq_top_iff]
  intro y _
  have : (y : Y ⧸ N') ∈ (⊤ : Subgroup (Y ⧸ N')) := Subgroup.mem_top _
  rw [hn, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at this
  exact this

theorem blockU_eq_V (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hS : IsShort2 (img (sporN H K) (conjClosure L M))) : blockU (conjClosure L M) = V := by
  refine le_antisymm ?_ (V_le_blockU h)
  set L₀ := conjClosure L M with hL₀
  set N := sporN H K
  have hirr := hS.2.2.2.2.2
  have hWU : img N V ⊔ blockZ (img N L₀) ≤ blockU (img N L₀) := by
    refine sup_le ?_ inf_le_left
    rw [blockU_img h h31]
    exact img_mono (V_le_blockU h)
  have hWN : img N L₀ ≤
      Subgroup.normalizer ((img N V ⊔ blockZ (img N L₀) : Subgroup _) : Set _) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (img_le_normalizer (M0_le_normalizer_V h) hl),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_blockZ' _ hl)]
  rcases hirr _ le_sup_right hWU hWN with hW | hW
  · exfalso
    apply img_V_ne_bot h h31
    rw [← img_V_comm h h31, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l hl
    have hvZ : v ∈ blockZ (img N L₀) := hW ▸ Subgroup.mem_sup_left hv
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hvZ.2 l hl).symm
  · have hVZ : V ⊔ blockZ L₀ ≤ sporX H K := sup_le (V_le_sporX h h31) (inf_le_left.trans
      (blockU_le_sporX h h31))
    have hcomm : ⁅blockU L₀, L₀⁆ ≤ V := by
      rw [Subgroup.commutator_le]
      intro u hu l hl
      have huX := blockU_le_sporX h h31 hu
      have hmk : ((⟨u, huX⟩ : ↥(sporX H K)) : ↥(sporX H K) ⧸ N) ∈ img N (V ⊔ blockZ L₀) := by
        rw [img_sup (V_le_sporX h h31) (blockZ_le_sporX h h31), ← blockZ_img h h31, hW,
          blockU_img h h31]
        exact mk_mem_img hu
      obtain ⟨w, hw, hwu⟩ := mem_img.1 hmk
      have hc := QuotientGroup.eq.mp hwu
      rw [mem_sporN] at hc
      have hc' : (w : G)⁻¹ * u ∈ Subgroup.centralizer (K : Set G) := by simpa using hc
      have hwK : (w : G) ∈ K := h31.1 (sup_le h.V_le (inf_le_left.trans (blockU_le_M0 _)) hw)
      have hlK : l ∈ K := h31.1 hl
      set c := (w : G)⁻¹ * u with hcdef
      have hu' : u = w * c := by rw [hcdef]; group
      have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc' l hlK).symm
      have hcw : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hc' w hwK).symm
      have hcomm' : ⁅u, l⁆ = ⁅(w : G), l⁆ := by
        rw [hu', commutatorElement_def, commutatorElement_def]
        calc (w : G) * c * l * ((w : G) * c)⁻¹ * l⁻¹ = w * (c * l) * c⁻¹ * (w : G)⁻¹ * l⁻¹ := by
              group
          _ = w * (l * c) * c⁻¹ * (w : G)⁻¹ * l⁻¹ := by rw [hcl]
          _ = w * l * (w : G)⁻¹ * l⁻¹ := by group
      rw [hcomm']
      have hZV : blockZ L₀ ≤ Subgroup.centralizer (V : Set G) :=
        inf_le_right.trans (Subgroup.centralizer_le h.V_le)
      have hZL : blockZ L₀ ≤ Subgroup.centralizer (L₀ : Set G) := inf_le_right
      have := commutator_sup_le_of_centralizes hZV hZL
        (Subgroup.commutator_mem_commutator hw hl)
      rwa [h.V_comm] at this
    have hUU : blockU L₀ = ⁅blockU L₀, L₀⁆ :=
      MS93.commutator_eq_commutator_commutator (CFSG.LieType.BorelTits.pCoreOf_le 2 _) le_rfl
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) Subgroup.le_normalizer
        (C2Nine.perfect_conjClosure_of_hyp h)
    rw [hUU]
    exact hcomm

omit [Finite G] in
theorem mem_of_mk_mem_img (h31 : C31Basic H R M L V K)
    {W : Subgroup G} (hZW : blockZ (conjClosure L M) ≤ W) (hWU : W ≤ blockU (conjClosure L M))
    {u : ↥(sporX H K)} (huU : (u : G) ∈ blockU (conjClosure L M))
    (hu : (u : ↥(sporX H K) ⧸ sporN H K) ∈ img (sporN H K) W) : (u : G) ∈ W := by
  obtain ⟨w, hw, hwu⟩ := mem_img.1 hu
  have hc := QuotientGroup.eq.mp hwu
  rw [mem_sporN] at hc
  have hc' : (w : G)⁻¹ * u ∈ Subgroup.centralizer (K : Set G) := by simpa using hc
  have hcU : (w : G)⁻¹ * u ∈ blockU (conjClosure L M) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hWU hw)) huU
  have hcZ : (w : G)⁻¹ * u ∈ blockZ (conjClosure L M) :=
    ⟨hcU, Subgroup.centralizer_le h31.1 hc'⟩
  have := W.mul_mem hw (hZW hcZ)
  simpa using this

theorem isShort2_of_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hS : IsShort2 (img (sporN H K) (conjClosure L M))) : IsShort2 (conjClosure L M) := by
  have hUV := blockU_eq_V h h31 hS
  set L₀ := conjClosure L M with hL₀
  set N := sporN H K
  have hL0X := M0_le_sporX h h31
  have hperf : commutator ↥L₀ = ⊤ := by
    rw [_root_.commutator_def]
    apply Subgroup.map_injective L₀.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      C2Nine.perfect_conjClosure_of_hyp h]
  obtain ⟨-, hchar, -, hq, ⟨hZU, hirr⟩⟩ := hS
  refine ⟨fun N' _ hp => eq_top_of_isPGroup_quotient hperf N' hp, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  ·
    rintro x ⟨hxL, hxC⟩
    have hxX := hL0X hxL
    have hmk : ((⟨x, hxX⟩ : ↥(sporX H K)) : ↥(sporX H K) ⧸ N) ∈
        img N L₀ ⊓ Subgroup.centralizer (pCoreOf 2 (img N L₀) : Set (↥(sporX H K) ⧸ N)) := by
      refine ⟨mk_mem_img hxL, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      rw [← img_pCoreOf hL0X (isPGroup_ker_M0 h h31)] at hb
      obtain ⟨o, ho, rfl⟩ := mem_img.1 hb
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC o ho)
    have h1 := hchar hmk
    rw [← img_pCoreOf hL0X (isPGroup_ker_M0 h h31)] at h1
    obtain ⟨o, ho, hox⟩ := mem_img.1 h1
    have hc := QuotientGroup.eq.mp hox
    rw [mem_sporN] at hc
    have hc' : (o : G)⁻¹ * x ∈ Subgroup.centralizer (K : Set G) := by simpa using hc
    have hoL := CFSG.LieType.BorelTits.pCoreOf_le 2 L₀ ho
    have h2 := M0_inf_centralizer_le h31
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hoL) hxL, hc'⟩
    have := Subgroup.mul_mem _ ho h2
    simpa using this
  ·
    rw [hUV]
    refine le_inf (V_le_blockQ h) fun v hv => Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    have hRL : R ≤ Subgroup.normalizer (L₀ : Set G) := h.le_M.trans (le_normalizer_conjClosure L M)
    have hq' := C48Pf.pCoreOf_le_pCoreOf_sup hRL hq
    exact (Subgroup.mem_centralizer_iff.mp (h.V_center hv).2 q hq')
  ·
    rw [hUV]
    exact h.V_elem.2
  ·
    rcases hq with hq | hq
    · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv (modO2EquivL h h31).symm hq)
    · exact Or.inr ((Nat.card_congr (modO2EquivL h h31).toEquiv).trans hq)
  ·
    refine lt_of_le_of_ne inf_le_left fun hEq => hZU.ne ?_
    rw [blockZ_img h h31, blockU_img h h31, hEq]
  ·
    intro W hZW hWU hWN
    have hWX : W ≤ sporX H K := hWU.trans (blockU_le_sporX h h31)
    have hZW' : blockZ (img N L₀) ≤ img N W := by rw [blockZ_img h h31]; exact img_mono hZW
    have hWU' : img N W ≤ blockU (img N L₀) := by rw [blockU_img h h31]; exact img_mono hWU
    rcases hirr _ hZW' hWU' (img_le_normalizer hWN) with h1 | h1
    · left
      refine le_antisymm (fun w hw => ?_) hZW
      have hwX := hWX hw
      have hmk : ((⟨w, hwX⟩ : ↥(sporX H K)) : ↥(sporX H K) ⧸ N) ∈ img N (blockZ L₀) := by
        rw [← blockZ_img h h31, ← h1]
        exact mk_mem_img hw
      exact mem_of_mk_mem_img h31 le_rfl inf_le_left (hWU hw) hmk
    · right
      refine le_antisymm hWU (fun u hu => ?_)
      have huX := blockU_le_sporX h h31 hu
      have hmk : ((⟨u, huX⟩ : ↥(sporX H K)) : ↥(sporX H K) ⧸ N) ∈ img N W := by
        rw [h1, blockU_img h h31]
        exact mk_mem_img hu
      exact mem_of_mk_mem_img h31 hZW hWU hu hmk

@[expose] noncomputable def blockUHom (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    ↥(blockU (conjClosure L M)) →* ↥(blockU (img (sporN H K) (conjClosure L M))) :=
  (MulEquiv.subgroupCongr (blockU_img h h31).symm).toMonoidHom.comp
    (imgHom (blockU_le_sporX h h31))

theorem coe_blockUHom (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (u : ↥(blockU (conjClosure L M))) :
    ((blockUHom h h31 u : ↥(blockU (img (sporN H K) (conjClosure L M)))) :
      ↥(sporX H K) ⧸ sporN H K) = ((⟨u, blockU_le_sporX h h31 u.2⟩ : ↥(sporX H K)) :
        ↥(sporX H K) ⧸ sporN H K) := rfl

theorem blockUHom_surjective (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    Function.Surjective (blockUHom h h31) := by
  rw [blockUHom, MonoidHom.coe_comp]
  exact (MulEquiv.surjective _).comp (imgHom_surjective _)

theorem comap_blockUHom (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    ((blockZ (img (sporN H K) (conjClosure L M))).subgroupOf
        (blockU (img (sporN H K) (conjClosure L M)))).comap (blockUHom h h31) =
      (blockZ (conjClosure L M)).subgroupOf (blockU (conjClosure L M)) := by
  ext u
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, coe_blockUHom]
  constructor
  · exact mem_blockZ_of_mk h h31 u.2
  · intro hu
    rw [blockZ_img h h31]
    exact mk_mem_img hu

theorem comap_pCore_imgHom_M0 (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    (CFSG.pCore 2 ↥(img (sporN H K) (conjClosure L M))).comap
      (imgHom (N := sporN H K) (M0_le_sporX h h31)) = CFSG.pCore 2 ↥(conjClosure L M) := by
  rw [← ker_mk_comp_imgHom (M0_le_sporX h h31) (isPGroup_ker_M0 h h31), ← MonoidHom.comap_ker,
    QuotientGroup.ker_mk']

theorem index_blockZ_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    ((blockZ (conjClosure L M)).subgroupOf (blockU (conjClosure L M))).index =
      ((blockZ (img (sporN H K) (conjClosure L M))).subgroupOf
        (blockU (img (sporN H K) (conjClosure L M)))).index := by
  rw [← comap_blockUHom h h31, Subgroup.index_comap_of_surjective _ (blockUHom_surjective h h31)]

theorem isAltBlockType_of_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) {m : ℕ}
    (hb : IsAltBlockType (img (sporN H K) (conjClosure L M)) m) :
    IsAltBlockType (conjClosure L M) m := by
  obtain ⟨hS, α, hα, hαk, β, hβ, hβk, heq⟩ := hb
  have hL0X := M0_le_sporX h h31
  refine ⟨isShort2_of_img h h31 hS, α.comp (imgHom hL0X), hα.comp (imgHom_surjective hL0X), ?_,
    β.comp (blockUHom h h31), hβ.comp (blockUHom_surjective h h31), ?_, fun ℓ u v huv => ?_⟩
  · rw [← MonoidHom.comap_ker, hαk, comap_pCore_imgHom_M0 h h31]
  · rw [← MonoidHom.comap_ker, hβk, comap_blockUHom h h31]
  · refine heq (imgHom hL0X ℓ) (blockUHom h h31 u) (blockUHom h h31 v) ?_
    have key := imgHom_conj (N := sporN H K) hL0X (blockU_le_sporX h h31) huv
    rw [coe_blockUHom, coe_blockUHom]
    simpa [coe_imgHom] using key

theorem isExcA7Block_of_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hb : IsExcA7Block (img (sporN H K) (conjClosure L M))) : IsExcA7Block (conjClosure L M) := by
  obtain ⟨hS, ⟨α, hα, hαk⟩, hidx⟩ := hb
  have hL0X := M0_le_sporX h h31
  refine ⟨isShort2_of_img h h31 hS, ⟨α.comp (imgHom hL0X), hα.comp (imgHom_surjective hL0X), ?_⟩,
    ?_⟩
  · rw [← MonoidHom.comap_ker, hαk, comap_pCore_imgHom_M0 h h31]
  · rw [index_blockZ_img h h31, hidx]

theorem isG2Block_of_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hb : IsG2Block (img (sporN H K) (conjClosure L M))) : IsG2Block (conjClosure L M) := by
  obtain ⟨hS, hpsu, hidx, α, hα, hαk, β, hβ, hβk, heq⟩ := hb
  have hL0X := M0_le_sporX h h31
  refine ⟨isShort2_of_img h h31 hS, ?_, ?_,
    α.comp (imgHom hL0X), hα.comp (imgHom_surjective hL0X), ?_,
    β.comp (blockUHom h h31), hβ.comp (blockUHom_surjective h h31), ?_, ?_⟩
  · exact Setup.Family.statedClassicalModel_of_mulEquiv (modO2EquivL h h31).symm hpsu
  · rw [index_blockZ_img h h31, hidx]
  · rw [← MonoidHom.comap_ker, hαk, comap_pCore_imgHom_M0 h h31]
  · rw [← MonoidHom.comap_ker, hβk, comap_blockUHom h h31]
  · intro ℓ u v representative huv hu
    apply heq (imgHom hL0X ℓ) (blockUHom h h31 u) (blockUHom h h31 v) representative
    · have key := imgHom_conj (N := sporN H K) hL0X (blockU_le_sporX h h31) huv
      rw [coe_blockUHom, coe_blockUHom]
      simpa [coe_imgHom] using key
    · exact hu

end CFSG.Quasithin.C48Spor
