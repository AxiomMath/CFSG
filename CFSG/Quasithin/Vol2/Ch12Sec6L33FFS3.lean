module

public import CFSG.Quasithin.Background.F918P3
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Vol2.Ch12Sec6Final

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin S126 Equiv
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Sections

theorem not_isStrongFFModule_of_subsingleton {V : Type} [CommGroup V] (hV : Subsingleton V)
    (X : Subgroup (MulAut V)) : ¬ IsStrongFFModule X := by
  haveI : Subsingleton (MulAut V) := ⟨fun φ ψ => MulEquiv.ext fun v => Subsingleton.elim _ _⟩
  rintro ⟨A, -, hne, -, -⟩
  apply hne
  rw [eq_bot_iff]
  intro φ _
  rw [Subgroup.mem_bot]
  exact Subsingleton.elim φ 1

theorem comm_flip_mem {P : Subgroup G} {b q : G} (h : b * q * b⁻¹ * q⁻¹ ∈ P) :
    q * b * q⁻¹ * b⁻¹ ∈ P := by
  have := P.inv_mem h
  simpa [mul_assoc] using this

variable {A B H : Subgroup G}

theorem actH_pCore_eq_one (hAH : H ≤ Subgroup.normalizer (A : Set G))
    (hBH : H ≤ Subgroup.normalizer (B : Set G))
    (hcomm : ∀ b ∈ B, ∀ q ∈ pCoreOf 2 H, q * b * q⁻¹ * b⁻¹ ∈ A) :
    ∀ q ∈ CFSG.pCore 2 ↥H, actH hAH hBH q = 1 := by
  intro q hq
  have hqG : (q : G) ∈ pCoreOf 2 H := Subgroup.mem_map.2 ⟨q, hq, rfl⟩
  ext w
  rw [MulAut.one_apply]
  obtain ⟨b, hbB, hb⟩ := mem_secImg.1 w.2
  rw [actH_apply_coe, ← hb, ← map_inv, ← map_mul, ← map_mul, secMk_eq_secMk_iff]
  have key := hcomm (b : G)⁻¹ (B.inv_mem hbB) (q : G) hqG
  convert key using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem isFFModule_actH_of_isFFInt {X : Subgroup G} (hXH : X ≤ H)
    (hAH : H ≤ Subgroup.normalizer (A : Set G)) (hBH : H ≤ Subgroup.normalizer (B : Set G))
    {hE : IsElemAbelian 2 (tildeOf A B)} (h : IsFFInt (tildeOf A X) (tildeOf A B) hE) :
    @IsFFModule ↥(tildeOf A B) (commGroupOfElemAbelian hE) (actH hAH hBH).range := by
  obtain ⟨A', hA', hne, hel, hle⟩ := h
  refine ⟨A', hA'.trans ?_, hne, hel, hle⟩
  rw [autOn_tilde_eq_map_actH hAH hBH hXH]
  exact (Subgroup.map_le_range _ _).trans le_rfl

theorem isStrongFFModule_actH_of_isStrongFFInt {X : Subgroup G} (hXH : X ≤ H)
    (hAH : H ≤ Subgroup.normalizer (A : Set G)) (hBH : H ≤ Subgroup.normalizer (B : Set G))
    {hE : IsElemAbelian 2 (tildeOf A B)} (h : F9.IsStrongFFInt (tildeOf A X) (tildeOf A B) hE) :
    @IsStrongFFModule ↥(tildeOf A B) (commGroupOfElemAbelian hE) (actH hAH hBH).range := by
  obtain ⟨A', hA', hne, hel, hlt⟩ := h
  refine ⟨A', hA'.trans ?_, hne, hel, hlt⟩
  rw [autOn_tilde_eq_map_actH hAH hBH hXH]
  exact (Subgroup.map_le_range _ _).trans le_rfl

def secPreimage (A : Subgroup G)
    (C : Subgroup (SecQuot (Subgroup.normalizer (A : Set G)) A)) : Subgroup G :=
  (C.comap (secMk (Subgroup.normalizer (A : Set G)) A)).map
    (Subgroup.normalizer (A : Set G)).subtype

omit [Finite G] in
theorem secPreimage_le (A : Subgroup G)
    (C : Subgroup (SecQuot (Subgroup.normalizer (A : Set G)) A)) :
    secPreimage A C ≤ Subgroup.normalizer (A : Set G) := by
  rintro _ ⟨p, -, rfl⟩
  exact p.2

omit [Finite G] in
theorem mem_secPreimage (A : Subgroup G)
    (C : Subgroup (SecQuot (Subgroup.normalizer (A : Set G)) A))
    {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ secPreimage A C ↔ secMk (Subgroup.normalizer (A : Set G)) A ⟨g, hg⟩ ∈ C := by
  constructor
  · rintro ⟨p, hp, hpg⟩
    have hpe : p = ⟨g, hg⟩ := Subtype.ext hpg
    rw [← hpe]
    exact hp
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem comm_comm_le_of_fix {hE : IsElemAbelian 2 (tildeOf A B)}
    (hAH : H ≤ Subgroup.normalizer (A : Set G))
    (hBH : H ≤ Subgroup.normalizer (B : Set G)) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    {K : Subgroup G} {t : G} (hKH : K ≤ H) (hK₂H : conjSub t⁻¹ K ≤ H)
    (hρ : CFSG.pCore 2 ↥H ≤ (actH hAH hBH).ker)
    (hfix : @commV ↥(tildeOf A B) (commGroupOfElemAbelian hE) ((S126.star H K).map
        (QuotientGroup.lift (CFSG.pCore 2 ↥H) (actH hAH hBH) hρ)) ≤
      @fixV ↥(tildeOf A B) (commGroupOfElemAbelian hE) ((S126.star H (conjSub t⁻¹ K)).map
        (QuotientGroup.lift (CFSG.pCore 2 ↥H) (actH hAH hBH) hρ))) :
    ⁅⁅B, K⁆, conjSub t⁻¹ K⁆ ≤ A := by
  obtain ⟨ρs, hρs⟩ : ∃ ρs, ρs = QuotientGroup.lift (CFSG.pCore 2 ↥H) (actH hAH hBH) hρ :=
    ⟨_, rfl⟩
  rw [← hρs] at hfix
  obtain ⟨C, hC⟩ : ∃ C : Subgroup (SecQuot (Subgroup.normalizer (A : Set G)) A),
      C = (@commV ↥(tildeOf A B) (commGroupOfElemAbelian hE)
        ((S126.star H K).map ρs)).map (tildeOf A B).subtype := ⟨_, rfl⟩
  have hxb : ∀ x : G, x ∈ K → ∀ b : G, b ∈ B → ⁅x, b⁆ ∈ secPreimage A C := by
    intro x hx b hb
    have hxH : x ∈ H := hKH hx
    have hxP : x ∈ Subgroup.normalizer (A : Set G) := hAH hxH
    have hbP : b ∈ Subgroup.normalizer (A : Set G) := hBA hb
    have hcP : ⁅x, b⁆ ∈ Subgroup.normalizer (A : Set G) := by
      rw [commutatorElement_def]
      exact (Subgroup.normalizer (A : Set G)).mul_mem
        ((Subgroup.normalizer (A : Set G)).mul_mem
          ((Subgroup.normalizer (A : Set G)).mul_mem hxP hbP)
          ((Subgroup.normalizer (A : Set G)).inv_mem hxP))
        ((Subgroup.normalizer (A : Set G)).inv_mem hbP)
    rw [mem_secPreimage A C hcP, hC]
    have hxbar : (QuotientGroup.mk ⟨x, hxH⟩ : S126.HStar H) ∈ S126.star H K :=
      ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    have hvb : secMk (Subgroup.normalizer (A : Set G)) A ⟨b, hbP⟩ ∈
        secImg (Subgroup.normalizer (A : Set G)) A B := secMk_mem_secImg hb
    obtain ⟨vb, hvb'⟩ : ∃ vb : ↥(tildeOf A B), (vb : SecQuot _ _) =
        secMk (Subgroup.normalizer (A : Set G)) A ⟨b, hbP⟩ := ⟨⟨_, hvb⟩, rfl⟩
    have hw : ρs (QuotientGroup.mk ⟨x, hxH⟩) vb * vb⁻¹ ∈
        @commV ↥(tildeOf A B) (commGroupOfElemAbelian hE) ((S126.star H K).map ρs) :=
      Subgroup.subset_closure ⟨ρs (QuotientGroup.mk ⟨x, hxH⟩),
        Subgroup.mem_map.2 ⟨_, hxbar, rfl⟩, vb, rfl⟩
    refine Subgroup.mem_map.2 ⟨_, hw, ?_⟩
    rw [hρs, QuotientGroup.lift_mk]
    show (((actH hAH hBH ⟨x, hxH⟩ vb * vb⁻¹ : ↥(tildeOf A B))) :
        SecQuot (Subgroup.normalizer (A : Set G)) A) = _
    rw [Subgroup.coe_mul, Subgroup.coe_inv, actH_apply_coe, hvb']
    simp only [← map_inv, ← map_mul]
    congr 1
  have hBK : ⁅B, K⁆ ≤ secPreimage A C := by
    refine Subgroup.commutator_le.mpr (fun (b : G) (hb : b ∈ B) (x : G) (hx : x ∈ K) => ?_)
    have h1 := (secPreimage A C).inv_mem (hxb x hx b hb)
    rwa [commutatorElement_inv] at h1
  refine Subgroup.commutator_le.mpr (fun (a : G) (ha : a ∈ ⁅B, K⁆) (y : G) (hy : y ∈ conjSub t⁻¹ K) => ?_)
  have haP : a ∈ Subgroup.normalizer (A : Set G) := secPreimage_le A C (hBK ha)
  have hsec := (mem_secPreimage A C haP).1 (hBK ha)
  rw [hC] at hsec
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.1 hsec
  have hyH : y ∈ H := hK₂H hy
  have hyP : y ∈ Subgroup.normalizer (A : Set G) := hAH hyH
  have hybar : (QuotientGroup.mk ⟨y, hyH⟩ : S126.HStar H) ∈ S126.star H (conjSub t⁻¹ K) :=
    ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  have hfixw : ρs (QuotientGroup.mk ⟨y, hyH⟩) w = w :=
    ((@mem_fixV ↥(tildeOf A B) (commGroupOfElemAbelian hE) _ _).1 (hfix hw))
      _ (Subgroup.mem_map.2 ⟨_, hybar, rfl⟩)
  have hwe' : (w : SecQuot (Subgroup.normalizer (A : Set G)) A) =
      secMk (Subgroup.normalizer (A : Set G)) A ⟨a, haP⟩ := hwe
  have h2 : secMk (Subgroup.normalizer (A : Set G)) A ⟨y, hyP⟩ *
      secMk (Subgroup.normalizer (A : Set G)) A ⟨a, haP⟩ *
      (secMk (Subgroup.normalizer (A : Set G)) A ⟨y, hyP⟩)⁻¹ =
      secMk (Subgroup.normalizer (A : Set G)) A ⟨a, haP⟩ := by
    have := congrArg (fun z : ↥(tildeOf A B) => (z : SecQuot (Subgroup.normalizer (A : Set G)) A))
      hfixw
    rw [hρs, QuotientGroup.lift_mk, actH_apply_coe, hwe'] at this
    exact this
  have h2' : secMk (Subgroup.normalizer (A : Set G)) A
      (⟨y, hyP⟩ * ⟨a, haP⟩ * ⟨y, hyP⟩⁻¹) = secMk (Subgroup.normalizer (A : Set G)) A ⟨a, haP⟩ := by
    rw [map_mul, map_mul, map_inv]
    exact h2
  rw [secMk_eq_secMk_iff] at h2'
  have h3 : ((y : G) * a * (y : G)⁻¹)⁻¹ * a ∈ A := by
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h2'
  rw [commutatorElement_def]
  have e : a * y * a⁻¹ * y⁻¹ = a * (((y : G) * a * (y : G)⁻¹)⁻¹ * a) * a⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 haP _).1 h3

theorem comm_of_actH_eq_one (hAH : H ≤ Subgroup.normalizer (A : Set G))
    (hBH : H ≤ Subgroup.normalizer (B : Set G)) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    {x : G} (hx : x ∈ H) (h1 : actH hAH hBH ⟨x, hx⟩ = 1) (b : G) (hb : b ∈ B) :
    x * b * x⁻¹ * b⁻¹ ∈ A := by
  have hc : ∀ c ∈ B, (x * c * x⁻¹)⁻¹ * c ∈ A := by
    intro c hc
    have hcP : c ∈ Subgroup.normalizer (A : Set G) := hBA hc
    have hw : actH hAH hBH ⟨x, hx⟩ ⟨secMk (Subgroup.normalizer (A : Set G)) A ⟨c, hcP⟩,
        secMk_mem_secImg hc⟩ = ⟨secMk (Subgroup.normalizer (A : Set G)) A ⟨c, hcP⟩,
        secMk_mem_secImg hc⟩ := by
      rw [h1]
      rfl
    have := congrArg (fun z : ↥(tildeOf A B) => (z : SecQuot (Subgroup.normalizer (A : Set G)) A))
      hw
    rw [actH_apply_coe] at this
    rw [← map_inv, ← map_mul, ← map_mul, secMk_eq_secMk_iff] at this
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have := hc b⁻¹ (B.inv_mem hb)
  convert this using 1
  group

theorem exists_actH_ne_one (hAH : H ≤ Subgroup.normalizer (A : Set G))
    (hBH : H ≤ Subgroup.normalizer (B : Set G)) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    {K₀ : Subgroup G} (hK0H : K₀ ≤ H) (hnt : ¬ ⁅B, K₀⁆ ≤ A) :
    ∃ k ∈ K₀, ∃ hk : k ∈ H, actH hAH hBH ⟨k, hk⟩ ≠ 1 := by
  by_contra hcon
  apply hnt
  refine Subgroup.commutator_le.mpr (fun (b : G) (hb : b ∈ B) (k : G) (hk : k ∈ K₀) => ?_)
  have hkH : k ∈ H := hK0H hk
  have h1 : actH hAH hBH ⟨k, hkH⟩ = 1 := by
    by_contra hne
    exact hcon ⟨k, hk, hkH, hne⟩
  have := comm_of_actH_eq_one hAH hBH hBA hkH h1 b hb
  rw [← commutatorElement_inv]
  exact A.inv_mem (by rw [commutatorElement_def]; exact this)

theorem sq_eq_one_of_isElemAbelian {X : Subgroup G} (hE : IsElemAbelian 2 X)
    (v : ↥X) : v ^ 2 = 1 := by
  apply Subtype.ext
  simpa using hE.2 v.1 v.2

end Sections

end CFSG.Quasithin.H13.L1233
