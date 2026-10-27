module

public import CFSG.Quasithin.Background.C48SporImg
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.C31Basic

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def sporX (H K : Subgroup G) : Subgroup G := H ⊓ Subgroup.normalizer (K : Set G)

@[expose] def sporN (H K : Subgroup G) : Subgroup ↥(sporX H K) :=
  (Subgroup.centralizer (K : Set G)).subgroupOf (sporX H K)

theorem mem_sporN {H K : Subgroup G} {x : ↥(sporX H K)} :
    x ∈ sporN H K ↔ (x : G) ∈ Subgroup.centralizer (K : Set G) := Iff.rfl

theorem conj_mem_centralizer {K : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hc : c ∈ Subgroup.centralizer (K : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro k hk
  have hgk : g⁻¹ * k * g ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp hk
    simpa using this
  have h1 := hc _ hgk
  calc k * (g * c * g⁻¹) = g * (g⁻¹ * k * g * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * k := by group

instance sporN_normal (H K : Subgroup G) : (sporN H K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_sporN] at hn ⊢
  simpa using conj_mem_centralizer g.2.2 hn

theorem le_sporX {H K Y : Subgroup G} (hYH : Y ≤ H) (hYK : Y ≤ Subgroup.normalizer (K : Set G)) :
    Y ≤ sporX H K :=
  le_inf hYH hYK

theorem K_le_sporX {H K : Subgroup G} (hK : K ≤ H) : K ≤ sporX H K :=
  le_sporX hK Subgroup.le_normalizer

theorem mem_ker_imgHom_iff {H K Y : Subgroup G} (hY : Y ≤ sporX H K) (y : ↥Y) :
    y ∈ (imgHom (N := sporN H K) hY).ker ↔ (y : G) ∈ Subgroup.centralizer (K : Set G) :=
  mem_ker_imgHom hY y

theorem ker_imgHom_K {H K : Subgroup G} (hK : K ≤ sporX H K) :
    (imgHom (N := sporN H K) hK).ker = Subgroup.center ↥K := by
  ext k
  rw [mem_ker_imgHom_iff, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g
    exact Subtype.ext (by simpa using h g g.2)
  · intro h g hg
    simpa using congrArg Subtype.val (h ⟨g, hg⟩)

@[expose] noncomputable def kStarEquiv {H K : Subgroup G} (hK : K ≤ sporX H K) :
    ↥K ⧸ Subgroup.center ↥K ≃* ↥(img (sporN H K) K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_imgHom_K hK).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (imgHom_surjective hK))

theorem mem_centralizer_of_perfect {K : Subgroup G} (hperf : ⁅K, K⁆ = K) {x : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hx : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ Subgroup.centralizer (K : Set G)) :
    x ∈ Subgroup.centralizer (K : Set G) := by
  have hmemK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ K := fun k hk =>
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hxK k).mp hk) (K.inv_mem hk)
  let f : ↥K →* G :=
    { toFun := fun k => x * k * x⁻¹ * (k : G)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have hb := Subgroup.mem_centralizer_iff.mp (hx b b.2) (a : G)⁻¹ (K.inv_mem a.2)
        simp only [Subgroup.coe_mul]
        calc x * (a * b) * x⁻¹ * ((a : G) * b)⁻¹
            = x * a * x⁻¹ * ((x * b * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = x * a * x⁻¹ * ((a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹)) := by rw [hb]
          _ = x * a * x⁻¹ * (a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹) := by group }
  have hker : ⁅(⊤ : Subgroup ↥K), ⊤⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    change (x * a * x⁻¹ * (a : G)⁻¹) * (x * b * x⁻¹ * (b : G)⁻¹) =
      (x * b * x⁻¹ * (b : G)⁻¹) * (x * a * x⁻¹ * (a : G)⁻¹)
    exact (Subgroup.mem_centralizer_iff.mp (hx a a.2) _ (hmemK b b.2)).symm
  have htop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]
  rw [htop, top_le_iff] at hker
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : f ⟨k, hk⟩ = 1 := by
    have : (⟨k, hk⟩ : ↥K) ∈ f.ker := by rw [hker]; trivial
    exact this
  have h2 : x * k * x⁻¹ * k⁻¹ = 1 := h1
  calc k * x = (x * k * x⁻¹ * k⁻¹)⁻¹ * (x * k) := by group
    _ = x * k := by rw [h2, inv_one, one_mul]

theorem centralizer_kStar_eq_bot {H K : Subgroup G} (hperf : ⁅K, K⁆ = K) (hK : K ≤ sporX H K) :
    Subgroup.centralizer (img (sporN H K) K : Set (↥(sporX H K) ⧸ sporN H K)) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_sporN]
  refine mem_centralizer_of_perfect hperf x.2.2 fun k hk => ?_
  have hc := Subgroup.mem_centralizer_iff.mp ha _ (mk_mem_img (N := sporN H K)
    (x := ⟨k, hK hk⟩) hk)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_sporN] at hc
  have hc' : (x : G)⁻¹ * k⁻¹ * x * k ∈ Subgroup.centralizer (K : Set G) := by
    simpa [mul_assoc] using hc
  have hkx : k * (x : G) ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer hk) x.2.2
  have := conj_mem_centralizer hkx hc'
  have heq : k * (x : G) * ((x : G)⁻¹ * k⁻¹ * x * k) * (k * x)⁻¹ = x * k * (x : G)⁻¹ * k⁻¹ := by
    group
  rwa [heq] at this

theorem le_normalizer_commutator_left' (A B : Subgroup G) :
    A ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ a ∈ A, ∀ c ∈ ⁅A, B⁆, a * c * a⁻¹ ∈ ⁅A, B⁆ := by
    intro a ha c hc
    have hle : ⁅A, B⁆ ≤ (⁅A, B⁆).comap (MulAut.conj a).toMonoidHom := by
      rw [Subgroup.commutator_def, Subgroup.closure_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      show (MulAut.conj a).toMonoidHom ⁅x, y⁆ ∈ ⁅A, B⁆
      have e : (MulAut.conj a).toMonoidHom ⁅x, y⁆ = ⁅a * x, y⁆ * ⁅a, y⁆⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e]
      exact (⁅A, B⁆).mul_mem (Subgroup.commutator_mem_commutator (A.mul_mem ha hx) hy)
        ((⁅A, B⁆).inv_mem (Subgroup.commutator_mem_commutator ha hy))
    exact hle hc
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key a ha c hc, fun hc => ?_⟩
  have h1 := key a⁻¹ (A.inv_mem ha) _ hc
  have e : a⁻¹ * (a * c * a⁻¹) * a⁻¹⁻¹ = c := by group
  rwa [e] at h1

theorem le_normalizer_commutator_right' (A B : Subgroup G) :
    B ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.commutator_comm]
  exact le_normalizer_commutator_left' B A

section Hyp

variable [Finite G] {H R M L V K : Subgroup G}

theorem M_le_sporX (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) : M ≤ sporX H K :=
  le_sporX h.le_H h31.2.1

theorem R_le_sporX (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) : R ≤ sporX H K :=
  h.le_M.trans (M_le_sporX h h31)

theorem M0_le_sporX (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    conjClosure L M ≤ sporX H K :=
  (C2Nine.conjClosure_le_M h).trans (M_le_sporX h h31)

theorem L_le_sporX (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) : L ≤ sporX H K :=
  (le_conjClosure L M).trans (M0_le_sporX h h31)

theorem V_le_K (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) : V ≤ K :=
  h.V_le.trans h31.1

theorem V_le_sporX (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) : V ≤ sporX H K :=
  h.V_le.trans (M0_le_sporX h h31)

theorem mem_M_of_centralizer (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) {x : G}
    (hxH : x ∈ H) (hx : x ∈ Subgroup.centralizer (K : Set G)) : x ∈ M := by
  apply h.V_norm
  refine ⟨hxH, Subgroup.mem_normalizer_iff.mpr fun v => ?_⟩
  have hcomm : ∀ w ∈ V, x * w * x⁻¹ = w := fun w hw => by
    rw [(Subgroup.mem_centralizer_iff.mp hx w (V_le_K h h31 hw)).symm]
    group
  constructor
  · intro hv
    rwa [hcomm v hv]
  · intro hv
    have := hcomm _ hv
    have hv' : v = x * v * x⁻¹ := by
      calc v = x⁻¹ * (x * v * x⁻¹) * x := by group
        _ = x⁻¹ * (x * (x * v * x⁻¹) * x⁻¹) * x := by rw [this]
        _ = x * v * x⁻¹ := by group
    rwa [hv']

theorem M0_le_normalizer_V (h : HypC28 H R M L V) :
    conjClosure L M ≤ Subgroup.normalizer (V : Set G) := by
  have := le_normalizer_commutator_right' V (conjClosure L M)
  rwa [h.V_comm] at this

theorem img_V_ne_bot (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    img (sporN H K) V ≠ ⊥ := by
  intro hV
  apply h.V_ne
  rw [← h.V_comm, eq_bot_iff, Subgroup.commutator_le]
  intro v hv m hm
  have hvC : v ∈ Subgroup.centralizer (K : Set G) := by
    have hmk := mk_mem_img (N := sporN H K) (x := ⟨v, V_le_sporX h h31 hv⟩) hv
    rw [hV, Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_sporN] at hmk
    exact hmk
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.mp hvC m (h31.1 hm)).symm

theorem img_M0_perfect (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    ⁅img (sporN H K) (conjClosure L M), img (sporN H K) (conjClosure L M)⁆ =
      img (sporN H K) (conjClosure L M) := by
  rw [← img_commutator (M0_le_sporX h h31) (M0_le_sporX h h31),
    C2Nine.perfect_conjClosure_of_hyp h]

theorem img_V_comm (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    ⁅img (sporN H K) V, img (sporN H K) (conjClosure L M)⁆ = img (sporN H K) V := by
  rw [← img_commutator (V_le_sporX h h31) (M0_le_sporX h h31), h.V_comm]

omit [Finite G] in
theorem img_K_normal (H K : Subgroup G) : (img (sporN H K) K).Normal := by
  have hn : (K.subgroupOf (sporX H K)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp g.2.2 n).mp hn
  exact hn.map _ (QuotientGroup.mk'_surjective _)

theorem exists_cComp_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    ∃ L' ∈ cComp (img (sporN H K) M),
      img (sporN H K) (conjClosure L M) = conjClosure L' (img (sporN H K) M) := by
  refine ⟨img (sporN H K) L, img_mem_cComp (M_le_sporX h h31) h.comp ?_,
    img_conjClosure (L_le_sporX h h31) (M_le_sporX h h31)⟩
  intro hL
  apply img_V_ne_bot h h31
  rw [eq_bot_iff]
  refine (img_mono h.V_le).trans ?_
  rw [img_conjClosure (L_le_sporX h h31) (M_le_sporX h h31), hL]
  exact conjClosure_le fun _ _ z hz => by
    rw [Subgroup.mem_bot.mp hz]
    simp

end Hyp

end CFSG.Quasithin.C48Spor
