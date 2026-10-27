module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
public import CFSG.RankThree.PartOne.KS.ModelR
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Quasithin.Vol2.KGFactC31Orb

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 CFSG.Sporadic.HeldB
  CFSG.Sporadic.SmallOddCore CFSG.RankThree.PartOne _root_.Certificates

variable {A : Type} [Group A]

structure Setup (S M₀ R M V : Subgroup A) : Prop where
  hS : S.Normal
  hSs : IsSporadic .He ↥S
  hper : ⁅M₀, M₀⁆ = M₀
  hR2 : IsPGroup 2 ↥R
  hRM : R ≤ M
  hMN : M ≤ Subgroup.normalizer (M₀ : Set A)
  hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A)
  hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀))
  hVM₀ : V ≤ M₀
  hVne : V ≠ ⊥
  hV : IsElemAbelian 2 V
  hcomm : ⁅V, M₀⁆ = V
  hVc : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (M₀ ⊔ R))
  hNR : Subgroup.normalizer (R : Set A) ≤ M

namespace Setup

variable {S M₀ R M V : Subgroup A} (h : Setup S M₀ R M V)
include h

theorem hM₀V : M₀ ≤ Subgroup.normalizer (V : Set A) := le_normalizer_of_comm h.hcomm

theorem hVO [Finite A] : V ≤ pCoreOf 2 M₀ :=
  (orb_facts h.hR2 h.hRM h.hMN h.hM₀R h.hsyl h.hVM₀ h.hV h.hcomm h.hVc h.hNR).1

theorem hOR [Finite A] : pCoreOf 2 M₀ ≤ R :=
  (orb_facts h.hR2 h.hRM h.hMN h.hM₀R h.hsyl h.hVM₀ h.hV h.hcomm h.hVc h.hNR).2.1

theorem hVR [Finite A] : V ≤ R := h.hVO.trans h.hOR

theorem hRC [Finite A] : R ≤ Subgroup.centralizer (V : Set A) :=
  (orb_facts h.hR2 h.hRM h.hMN h.hM₀R h.hsyl h.hVM₀ h.hV h.hcomm h.hVc h.hNR).2.2.1

theorem hrad [Finite A] : pCoreOf 2 (Subgroup.normalizer (R : Set A)) = R :=
  pCoreOf_normalizer_eq h.hR2 h.hMN h.hM₀R h.hsyl h.hNR

theorem normal_in_normalizer : Subgroup.normalizer (R : Set A) ≤
    Subgroup.normalizer (M₀ : Set A) := h.hNR.trans h.hMN

theorem V_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
  have := h.hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

theorem V_le_cent : V ≤ Subgroup.centralizer (V : Set A) := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun y hy => h.V_comm y hy x hx

theorem R_ne_bot [Finite A] : R ≠ ⊥ := fun hR => h.hVne (eq_bot_iff.mpr (hR ▸ h.hVR))

end Setup

structure Emb (S : Subgroup A) (ι : A →* Equiv.Perm (Fin 8330)) : Prop where
  inj : Function.Injective ι
  mapS : S.map ι = heP
  le : ι.range ≤ heAutGroup

namespace Emb

variable {S : Subgroup A} {ι : A →* Equiv.Perm (Fin 8330)} (hι : Emb S ι)
include hι

theorem mem_heAutGroup (x : A) : ι x ∈ heAutGroup := hι.le ⟨x, rfl⟩

theorem mem_heP_iff (x : A) : ι x ∈ heP ↔ x ∈ S := by
  rw [← hι.mapS, Subgroup.mem_map_iff_mem hι.inj]

theorem mem_heP {x : A} (hx : x ∈ S) : ι x ∈ heP := (hι.mem_heP_iff x).2 hx

theorem map_comap {Y : Subgroup (Equiv.Perm (Fin 8330))} (hY : Y ≤ heP) :
    (Y.comap ι).map ι = Y := by
  rw [Subgroup.map_comap_eq]
  exact inf_eq_right.mpr (hY.trans (hι.mapS ▸ Subgroup.map_le_range ι S))

theorem comap_le_S {Y : Subgroup (Equiv.Perm (Fin 8330))} (hY : Y ≤ heP) : Y.comap ι ≤ S :=
  fun x hx => (hι.mem_heP_iff x).1 (hY hx)

theorem card_comap {Y : Subgroup (Equiv.Perm (Fin 8330))} (hY : Y ≤ heP) :
    Nat.card (Y.comap ι) = Nat.card Y := by
  rw [← Subgroup.card_map_of_injective hι.inj, hι.map_comap hY]

theorem conj {d : Equiv.Perm (Fin 8330)} (hd : d ∈ heAutGroup) :
    Emb S ((MulAut.conj d).toMonoidHom.comp ι) := by
  refine ⟨(MulAut.conj d).injective.comp hι.inj, ?_, ?_⟩
  · rw [← Subgroup.map_map, hι.mapS]
    ext x
    rw [Subgroup.mem_map]
    have hdN := heAutGroup_le_normalizer hd
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hdN y).mp hy
    · intro hx
      refine ⟨d⁻¹ * x * d, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) x).mp hx
      simpa [mul_assoc] using this
  · rintro _ ⟨x, rfl⟩
    exact heAutGroup.mul_mem (heAutGroup.mul_mem hd (hι.mem_heAutGroup x)) (heAutGroup.inv_mem hd)

end Emb

theorem heAutModel'
    : AutModel heP heAutGroup := by
  obtain ⟨hbij, -⟩ := ctbh_full_automorphism_permutation_model
  exact autModel_of_conj_equiv heP_le_heAutGroup heP_normal_heAutGroup
    (MulEquiv.ofBijective heConjR hbij) (fun x p => heConjR_apply x p)

theorem exists_emb
    {S : Subgroup A} (hSn : S.Normal) (hSs : IsSporadic .He ↥S)
    (hCS : Subgroup.centralizer (S : Set A) = ⊥) : ∃ ι, Emb S ι := by
  obtain ⟨e⟩ := hSs
  let θ : ↥S ≃* ↥heP := e.trans heEquivP
  have hM := heAutModel'
  refine ⟨hM.embed S θ, hM.embed_injective S θ hCS, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [show s = ((⟨s, hs⟩ : ↥S) : A) from rfl, hM.embed_coe S θ]
      exact (θ ⟨s, hs⟩).2
    · intro hx
      refine ⟨(θ.symm ⟨x, hx⟩ : ↥S), (θ.symm ⟨x, hx⟩).2, ?_⟩
      rw [hM.embed_coe S θ, MulEquiv.apply_symm_apply]
  · rintro _ ⟨x, rfl⟩
    exact hM.embed_mem S θ x

theorem card_S {S : Subgroup A} (hSs : IsSporadic .He ↥S) :
    Nat.card S = 4030387200 := by
  obtain ⟨e⟩ := hSs
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.He.card_He

theorem exists_sylow_le_he {X : Type} [Group X] [Finite X] (hX : Nat.card X = 4030387200)
    {Y : Subgroup X} (hY : 1024 ∣ Nat.card Y) : ∃ T : Subgroup X, IsSylowTwoOf T ⊤ ∧ T ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 Y))
  refine ⟨(P : Subgroup Y).map Y.subtype, ?_, ?_⟩
  · rw [K1.isSylowTwoOf_top_iff]
    refine ⟨P.isPGroup'.map Y.subtype, ?_⟩
    rw [Subgroup.index_map_subtype]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact P.not_dvd_index h
    · have h1 := Y.card_mul_index
      rw [hX] at h1
      obtain ⟨a, ha⟩ := hY
      obtain ⟨b, hb⟩ := h
      rw [ha, hb] at h1
      have h3 : 2048 ∣ 4030387200 := ⟨a * b, by rw [← h1]; ring⟩
      norm_num at h3
  · rintro _ ⟨x, -, rfl⟩
    exact x.2

theorem pCoreOf_map_subtype' (p : ℕ) (S : Subgroup A) (Y : Subgroup ↥S) :
    (pCoreOf p Y).map S.subtype = pCoreOf p (Y.map S.subtype) := by
  let e := Y.equivMapOfInjective S.subtype S.subtype_injective
  have hhom : (Y.map S.subtype).subtype.comp e.toMonoidHom = S.subtype.comp Y.subtype := by
    ext x
    rfl
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv p e, Subgroup.map_map, Subgroup.map_map,
    hhom]

theorem exists_mem_heMems [Finite A]
    {S R X : Subgroup A} (hSn : S.Normal) (hSs : IsSporadic .He ↥S) (hR2 : IsPGroup 2 ↥R)
    (hRS : R ≤ S) (hR1 : R ≠ ⊥) (hrad : pCoreOf 2 (Subgroup.normalizer (R : Set A)) = R)
    (hXN : X ≤ Subgroup.normalizer (R : Set A)) (hXS : X ≤ S) (hX : 1024 ∣ Nat.card X) :
    ∃ m ∈ Ch1.SporLat.He.heMems, Nat.card ↥(Subgroup.normalizer (R : Set A) ⊓ S) = m.order ∧
      Nat.card R = m.o2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := Subgroup.normalizer (R : Set A) ⊓ S with hN'
  have hRN' : R ≤ N' := le_inf Subgroup.le_normalizer hRS
  have hO : pCoreOf 2 N' = R := by
    refine le_antisymm ?_
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRN' inf_le_left hR2)
    have hle : pCoreOf 2 N' ≤ pCoreOf 2 (Subgroup.normalizer (R : Set A)) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 N').trans inf_le_left) ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N')
      intro x hx
      refine CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N' ?_
      refine mem_normalizer_inf (Subgroup.le_normalizer hx)
        (Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hSn.conj_mem y hy x, fun hy => ?_⟩)
      have := hSn.conj_mem _ hy x⁻¹
      simpa [mul_assoc] using this
    rwa [hrad] at hle
  set Y := N'.subgroupOf S with hY
  have hYmap : Y.map S.subtype = N' := by
    rw [hY, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hcardY : Nat.card Y = Nat.card N' := by
    rw [← hYmap, Subgroup.card_map_of_injective S.subtype_injective]
  have hOY : Nat.card (pCoreOf 2 Y) = Nat.card R := by
    rw [← hO, ← hYmap, ← pCoreOf_map_subtype', Subgroup.card_map_of_injective S.subtype_injective]
  have hXY : X.subgroupOf S ≤ Y := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (le_inf hXN hXS (Subgroup.mem_subgroupOf.mp hx))
  have hcardX : Nat.card (X.subgroupOf S) = Nat.card X := by
    rw [← Subgroup.card_map_of_injective S.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hXS]
  obtain ⟨T, hT, hTX⟩ := exists_sylow_le_he (card_S hSs) (Y := X.subgroupOf S)
    (by rw [hcardX]; exact hX)
  obtain ⟨e⟩ := hSs
  rcases Ch1.SporLat.He.he_overgroups ⟨e⟩ hT (hTX.trans hXY) with htop | ⟨m, hm, hord, ho2, -⟩
  ·
    exfalso
    have : IsSimpleGroup ↥S := @MulEquiv.isSimpleGroup _ _ _ _
      CFSG.Sporadic.He.isSimpleGroup_He e
    have hn : (R.subgroupOf S).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hg : (g : A) ∈ Subgroup.normalizer (R : Set A) := by
        have : g ∈ Y := by rw [htop]; trivial
        exact (Subgroup.mem_subgroupOf.mp this).1
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp hx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf S) with h | h
    · apply hR1
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hRS hx⟩ : ↥S) ∈ R.subgroupOf S := hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · have hSR : S ≤ R := fun x hx => by
        have : (⟨x, hx⟩ : ↥S) ∈ R.subgroupOf S := by rw [h]; trivial
        exact this
      have hS2 : IsPGroup 2 ↥S := hR2.to_le hSR
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
      rw [card_S ⟨e⟩] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 4030387200)
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  · exact ⟨m, hm, by rw [← hcardY]; exact hord, by rw [← hOY]; exact ho2⟩

end CFSG.Quasithin.KGC31.He

end
