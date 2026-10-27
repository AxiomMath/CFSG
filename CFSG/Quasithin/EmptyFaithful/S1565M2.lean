module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.F918P5
public import CFSG.Quasithin.EmptyFaithful.S1565A
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1565

section KerLe

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem toAutI_ker_le_kerIn (hF : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) (hne : autIH V₁ I H K ≠ ⊥) {M' : Subgroup G}
    (hkerchar : ∀ x : G, x ∈ kerIn M' H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) :
    ∀ k : ↥K, toAutI hF I k = 1 →
      Subgroup.inclusion (le_of_mem_cComp hF.K_cComp) k ∈ (kerIn M' H).subgroupOf H := by
  intro k hk
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hFI := factElem hF hIU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : IsSubnormal K H := subnormal_of_mem_cComp hF.K_cComp
  have hker0 : (pCoreOf 2 K).subgroupOf K ≤ (toAutI hF I).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, toAutI_eq_one_iff]
    exact hF.actH_eq_one_of_mem_pCoreOf hIU
      (A4.pCoreOf_le_of_subnormal 2 hsub (Subgroup.mem_subgroupOf.mp hx))
  let π : ↥K →* ↥K ⧸ (pCoreOf 2 K).subgroupOf K := QuotientGroup.mk' _
  let φ : ↥K ⧸ (pCoreOf 2 K).subgroupOf K →* ↥(autIH V₁ I H K) :=
    QuotientGroup.lift _ (toAutI hF I) hker0
  have hφnt : ∃ x, φ x ≠ 1 := by
    obtain ⟨y, hyS, hy1⟩ : ∃ y ∈ autIH V₁ I H K, y ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hne ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    obtain ⟨x, hx⟩ := toAutI_surjective hF I ⟨y, hyS⟩
    refine ⟨QuotientGroup.mk x, fun h => hy1 ?_⟩
    have h1 : toAutI hF I x = 1 := h
    rw [h1] at hx
    exact congrArg Subtype.val hx.symm
  have hcen := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hF.K_quasisimple hφnt
  have hkc' : π k ∈ Subgroup.center (↥K ⧸ (pCoreOf 2 K).subgroupOf K) :=
    hcen (by rw [MonoidHom.mem_ker]; exact hk)
  have hkc : ∀ k₁ : ↥K, (k : G) * (k₁ : G) * (k : G)⁻¹ * (k₁ : G)⁻¹ ∈ pCoreOf 2 H := by
    intro k₁
    have hc := Subgroup.mem_center_iff.mp hkc' (π k₁)
    have h1 : π (k * k₁ * k⁻¹ * k₁⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hc]
      group
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact A4.pCoreOf_le_of_subnormal 2 hsub (Subgroup.mem_subgroupOf.mp h2)
  let Ck : Subgroup ↥H :=
    { carrier := {y | (k : G) * (y : G) * (k : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 H}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have hQn : (a : G) ∈ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H a.2
        have e : (k : G) * ((a * b : ↥H) : G) * (k : G)⁻¹ * ((a * b : ↥H) : G)⁻¹ =
            ((k : G) * (a : G) * (k : G)⁻¹ * (a : G)⁻¹) *
              ((a : G) * ((k : G) * (b : G) * (k : G)⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        rw [Set.mem_ofPred_eq, e]
        refine (pCoreOf 2 H).mul_mem ha ?_
        exact (Subgroup.mem_normalizer_iff.mp hQn _).mp hb
      inv_mem' := by
        intro a ha
        have hQn : (a : G) ∈ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H a.2
        have e : (k : G) * ((a⁻¹ : ↥H) : G) * (k : G)⁻¹ * ((a⁻¹ : ↥H) : G)⁻¹ =
            (a : G)⁻¹ * ((k : G) * (a : G) * (k : G)⁻¹ * (a : G)⁻¹)⁻¹ * ((a : G)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_inv]
          group
        rw [Set.mem_ofPred_eq, e]
        have hQn' : (a : G)⁻¹ ∈ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
          Subgroup.inv_mem _ hQn
        exact (Subgroup.mem_normalizer_iff.mp hQn' _).mp ((pCoreOf 2 H).inv_mem ha) }
  have hKCk : K.subgroupOf H ≤ Ck := fun y hy => hkc ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
  have hQCk : (pCoreOf 2 H).subgroupOf H ≤ Ck := by
    intro y hy
    have hyQ : (y : G) ∈ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp hy
    have hkn : (k : G) ∈ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH k.2)
    have h1 : (k : G) * (y : G) * (k : G)⁻¹ ∈ pCoreOf 2 H := (Subgroup.mem_normalizer_iff.mp hkn _).mp hyQ
    exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hyQ)
  have hKQ : (K ⊔ pCoreOf 2 H).subgroupOf H ≤ Ck := by
    rw [Subgroup.subgroupOf_sup hKH (CFSG.LieType.BorelTits.pCoreOf_le 2 H)]
    exact sup_le hKCk hQCk
  rw [Subgroup.mem_subgroupOf]
  refine (hkerchar _).mpr ⟨Subgroup.mem_sup_left k.2, fun y hy => ?_⟩
  have hyH : y ∈ H := sup_le hKH (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hy
  exact hKQ (Subgroup.mem_subgroupOf.mpr hy : (⟨y, hyH⟩ : ↥H) ∈ (K ⊔ pCoreOf 2 H).subgroupOf H)

end KerLe

section Lift

variable {G : Type} [Group G]

private noncomputable def starMapM2 (M' H K : Subgroup G) (hKH : K ≤ H) :
    ↥K →* ↥(E2.star M' H K) :=
  (((QuotientGroup.mk' ((kerIn M' H).subgroupOf H)).comp (Subgroup.inclusion hKH)).codRestrict
    (E2.star M' H K) fun k => ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)

private theorem starMapM2_surjective (M' H K : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (starMapM2 M' H K hKH) := by
  rintro ⟨y, x, hx, rfl⟩
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  rfl

private theorem starMapM2_eq_one_iff (M' H K : Subgroup G) (hKH : K ≤ H) (k : ↥K) :
    starMapM2 M' H K hKH k = 1 ↔ Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).mp this
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr h

theorem exists_sylow_borel_lift_of_kernel {M' H K : Subgroup G} (hKH : K ≤ H) {L : Type} [Group L]
    [Finite L] (ρ : ↥K →* L) (hρ : Function.Surjective ρ)
    (hker : ∀ k : ↥K, ρ k = 1 → Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H)
    (hB : E2.IsBorelIn (E2.star M' H K) (E2.star M' H (M' ⊓ K))) :
    ∃ S : Sylow 2 L, ∀ b ∈ Subgroup.normalizer ((S : Subgroup L) : Set L),
      ∃ k : ↥K, (k : G) ∈ M' ∧ ρ k = b := by
  have hq := starMapM2_surjective M' H K hKH
  have hkq : ρ.ker ≤ (starMapM2 M' H K hKH).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, starMapM2_eq_one_iff]
    exact hker k hk
  let σ : L →* ↥(E2.star M' H K) :=
    ρ.liftOfRightInverse (Function.surjInv hρ) (Function.rightInverse_surjInv hρ)
      ⟨starMapM2 M' H K hKH, hkq⟩
  have hσρ : ∀ k, σ (ρ k) = starMapM2 M' H K hKH k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨_, hkq⟩ k
  have hσs : Function.Surjective σ := by
    intro y
    obtain ⟨k, rfl⟩ := hq y
    exact ⟨ρ k, hσρ k⟩
  obtain ⟨S₀, hS₀, hMKs⟩ := hB
  obtain ⟨hS₀K, hS₀2, hS₀i⟩ := hS₀
  have hS' : IsPGroup 2 (S₀.subgroupOf (E2.star M' H K)) :=
    hS₀2.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀K).symm
  let S₁ : Sylow 2 ↥(E2.star M' H K) := hS'.toSylow hS₀i
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hσs 2 S₁
  refine ⟨S, fun b hb => ?_⟩
  have hbmap := Subgroup.le_normalizer_map σ ⟨b, hb, rfl⟩
  have hSmap : (S : Subgroup L).map σ = (S₁ : Subgroup ↥(E2.star M' H K)) := by
    rw [← hS, Sylow.coe_mapSurjective]
  rw [hSmap] at hbmap
  obtain ⟨y, hy⟩ : ∃ y : ↥(E2.star M' H K), y = σ b := ⟨σ b, rfl⟩
  rw [← hy] at hbmap
  have hS₁mem : ∀ h : ↥(E2.star M' H K), h ∈ (S₁ : Subgroup ↥(E2.star M' H K)) ↔
      (h : E2.StarQuot M' H) ∈ S₀ := fun h => Iff.rfl
  have hyY : (y : E2.StarQuot M' H) ∈ Subgroup.normalizer (S₀ : Set (E2.StarQuot M' H)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hhS
      have hhK : h ∈ E2.star M' H K := hS₀K hhS
      have := (Subgroup.mem_normalizer_iff.mp hbmap ⟨h, hhK⟩).mp ((hS₁mem _).mpr hhS)
      exact (hS₁mem _).mp this
    · intro hS2'
      have hhK : h ∈ E2.star M' H K := by
        have h1 : (y : E2.StarQuot M' H)⁻¹ *
            ((y : E2.StarQuot M' H) * h * (y : E2.StarQuot M' H)⁻¹) * (y : E2.StarQuot M' H) = h := by
          group
        rw [← h1]
        exact (E2.star M' H K).mul_mem ((E2.star M' H K).mul_mem ((E2.star M' H K).inv_mem y.2)
          (hS₀K hS2')) y.2
      have := (Subgroup.mem_normalizer_iff.mp hbmap ⟨h, hhK⟩).mpr ((hS₁mem _).mpr hS2')
      exact (hS₁mem _).mp this
  have hmem : (y : E2.StarQuot M' H) ∈ E2.star M' H (M' ⊓ K) := by
    rw [hMKs]
    exact ⟨y.2, hyY⟩
  obtain ⟨x, hx, hxy⟩ := hmem
  have hxM : (x : G) ∈ M' ⊓ K := Subgroup.mem_subgroupOf.mp hx
  have hk0 : starMapM2 M' H K hKH ⟨(x : G), hxM.2⟩ = y := Subtype.ext hxy
  have hz : σ ((ρ ⟨(x : G), hxM.2⟩)⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, hσρ, hk0, hy]
    exact inv_mul_cancel _
  obtain ⟨k', hk'⟩ := hρ ((ρ ⟨(x : G), hxM.2⟩)⁻¹ * b)
  have hk'1 : starMapM2 M' H K hKH k' = 1 := by
    rw [← hσρ, hk']
    exact hz
  have hk'ker : (k' : G) ∈ kerIn M' H :=
    Subgroup.mem_subgroupOf.mp ((starMapM2_eq_one_iff M' H K hKH k').mp hk'1)
  refine ⟨⟨(x : G), hxM.2⟩ * k', ?_, ?_⟩
  · exact M'.mul_mem hxM.1 (kerIn_le hk'ker)
  · rw [map_mul, hk']
    group

end Lift

section Acting

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem exists_sylow_borel_acting_two (hF : HypF918 T V L V₁ Vp H K) (M I : Subgroup G)
    (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hkerchar : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    ∃ S : Sylow 2 ↥(autIH V₁ I H K),
      ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥(autIH V₁ I H K)) : Set ↥(autIH V₁ I H K)),
        ∃ k : ↥K, (k : G) ∈ M ∧ toAutI hF I k = b := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hFI := factElem hF hIU
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  have : Finite ↥(autIH V₁ I H K) := Finite.of_surjective _ (toAutI_surjective hF I)
  obtain ⟨S, hS⟩ := exists_sylow_borel_lift_of_kernel hKH (toAutI hF I) (toAutI_surjective hF I)
    (toAutI_ker_le_kerIn hF hIU hne hkerchar) hB
  refine ⟨S, fun b hb => ?_⟩
  obtain ⟨k, hkM, hkb⟩ := hS b hb
  exact ⟨k, (Subgroup.mem_inf.mp hkM).2, hkb⟩

end Acting

end CFSG.Quasithin
