module

public import CFSG.Quasithin.Background.D1Statement
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.SimsD1.TransGrp

open CFSG.Open CFSG.QuasithinUnique

section General

variable {A B : Type*} [Group A] [Group B]

theorem map_comap_of_le_map (f : A →* B) {H : Subgroup A} {K : Subgroup B} (h : K ≤ H.map f) :
    (K.comap f).map f = K :=
  Subgroup.map_comap_eq_self (h.trans (Subgroup.map_le_range f H))

theorem exists_map_eq_of_le_map (f : A →* B) {H : Subgroup A} {K : Subgroup B}
    (h : K ≤ H.map f) : ∃ L : Subgroup A, L.map f = K :=
  ⟨K.comap f, map_comap_of_le_map f h⟩

theorem comap_le_of_le_map (f : A →* B) (hf : Function.Injective f) {H : Subgroup A}
    {K : Subgroup B} (h : K ≤ H.map f) : K.comap f ≤ H := by
  have := Subgroup.comap_mono (f := f) h
  rwa [Subgroup.comap_map_eq_self_of_injective hf] at this

theorem mem_centralizer_map_iff (f : A →* B) (hf : Function.Injective f) (X : Subgroup A)
    (a : A) :
    f a ∈ Subgroup.centralizer ((X.map f : Subgroup B) : Set B) ↔
      a ∈ Subgroup.centralizer (X : Set A) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    apply hf
    rw [map_mul, map_mul]
    exact h (f x) ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, h x hx]

theorem mem_normalizer_map_iff (f : A →* B) (hf : Function.Injective f) (X : Subgroup A)
    (a : A) :
    f a ∈ Subgroup.normalizer ((X.map f : Subgroup B) : Set B) ↔
      a ∈ Subgroup.normalizer (X : Set A) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (H := X.map f) (f := f)
    (Subgroup.map_le_range f X)
  rw [Subgroup.comap_map_eq_self_of_injective hf] at h
  rw [← Subgroup.mem_comap, h]

theorem map_inf_centralizer_eq (f : A →* B) (hf : Function.Injective f) (K X : Subgroup A) :
    (K ⊓ Subgroup.centralizer (X : Set A)).map f =
      K.map f ⊓ Subgroup.centralizer ((X.map f : Subgroup B) : Set B) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨a, ⟨haK, haC⟩, rfl⟩
    exact ⟨⟨a, haK, rfl⟩, (mem_centralizer_map_iff f hf X a).2 haC⟩
  · rintro ⟨⟨a, haK, rfl⟩, hC⟩
    exact ⟨a, ⟨haK, (mem_centralizer_map_iff f hf X a).1 hC⟩, rfl⟩

theorem le_normalizer_map_iff (f : A →* B) (hf : Function.Injective f) (H X : Subgroup A) :
    H.map f ≤ Subgroup.normalizer ((X.map f : Subgroup B) : Set B) ↔
      H ≤ Subgroup.normalizer (X : Set A) := by
  rw [Subgroup.map_le_iff_le_comap]
  exact ⟨fun h a ha => (mem_normalizer_map_iff f hf X a).1 (h ha),
    fun h a ha => (mem_normalizer_map_iff f hf X a).2 (h ha)⟩

theorem le_centralizer_map_iff (f : A →* B) (hf : Function.Injective f) (H X : Subgroup A) :
    H.map f ≤ Subgroup.centralizer ((X.map f : Subgroup B) : Set B) ↔
      H ≤ Subgroup.centralizer (X : Set A) := by
  rw [Subgroup.map_le_iff_le_comap]
  exact ⟨fun h a ha => (mem_centralizer_map_iff f hf X a).1 (h ha),
    fun h a ha => (mem_centralizer_map_iff f hf X a).2 (h ha)⟩

theorem normal_subgroupOf_map_iff (f : A →* B) (hf : Function.Injective f) {X H : Subgroup A}
    (hXH : X ≤ H) :
    ((X.map f).subgroupOf (H.map f)).Normal ↔ (X.subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hXH),
    Subgroup.normal_subgroupOf_iff_le_normalizer hXH, le_normalizer_map_iff f hf]

theorem pCoreOf_map_eq (f : A →* B) (hf : Function.Injective f) (p : ℕ) (K : Subgroup A) :
    pCoreOf p (K.map f) = (pCoreOf p K).map f := by
  let e : ↥K ≃* ↥(K.map f) := K.equivMapOfInjective f hf
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem isPGroup_map_iff (f : A →* B) (hf : Function.Injective f) (p : ℕ) (K : Subgroup A) :
    IsPGroup p ↥(K.map f) ↔ IsPGroup p ↥K :=
  ⟨fun h => h.of_equiv (K.equivMapOfInjective f hf).symm,
    fun h => h.of_equiv (K.equivMapOfInjective f hf)⟩

theorem isElemAbelian_map_iff (f : A →* B) (hf : Function.Injective f) (p : ℕ)
    (K : Subgroup A) : IsElemAbelian p (K.map f) ↔ IsElemAbelian p K :=
  ⟨fun h => by
    simpa [Subgroup.comap_map_eq_self_of_injective hf] using IsElemAbelian.comap h hf,
    fun h => h.map f⟩

theorem isMaxElemAbelian_map_iff (f : A →* B) (hf : Function.Injective f) (H C : Subgroup A) :
    IsMaxElemAbelian (H.map f) (C.map f) ↔ IsMaxElemAbelian H C := by
  constructor
  · rintro ⟨hCH, hCE, hmax⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hf).1 hCH,
      (isElemAbelian_map_iff f hf 2 C).1 hCE, fun K hKH hKE => ?_⟩
    have h := hmax (K.map f) (Subgroup.map_mono hKH) ((isElemAbelian_map_iff f hf 2 K).2 hKE)
    rwa [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf] at h
  · rintro ⟨hCH, hCE, hmax⟩
    refine ⟨Subgroup.map_mono hCH, (isElemAbelian_map_iff f hf 2 C).2 hCE, fun K hKH hKE => ?_⟩
    have h1 := map_comap_of_le_map f hKH
    have hKE' : IsElemAbelian 2 (K.comap f) :=
      (isElemAbelian_map_iff f hf 2 (K.comap f)).1 (by rw [h1]; exact hKE)
    have h2 := hmax (K.comap f) (comap_le_of_le_map f hf hKH) hKE'
    rw [Subgroup.card_map_of_injective hf]
    calc Nat.card ↥K = Nat.card ↥((K.comap f).map f) := by rw [h1]
      _ = Nat.card ↥(K.comap f) := Subgroup.card_map_of_injective hf
      _ ≤ Nat.card ↥C := h2

theorem eq_map_comap_of_isMaxElemAbelian (f : A →* B) {H : Subgroup A} {D : Subgroup B}
    (hD : IsMaxElemAbelian (H.map f) D) : D = (D.comap f).map f :=
  (map_comap_of_le_map f hD.1).symm

theorem isMaxElemAbelian_map_iff_exists (f : A →* B) (hf : Function.Injective f)
    (H : Subgroup A) (D : Subgroup B) :
    IsMaxElemAbelian (H.map f) D ↔ ∃ C : Subgroup A, IsMaxElemAbelian H C ∧ C.map f = D := by
  constructor
  · intro hD
    refine ⟨D.comap f, ?_, (eq_map_comap_of_isMaxElemAbelian f hD).symm⟩
    have := hD
    rw [eq_map_comap_of_isMaxElemAbelian f hD] at this
    exact (isMaxElemAbelian_map_iff f hf H _).1 this
  · rintro ⟨C, hC, rfl⟩
    exact (isMaxElemAbelian_map_iff f hf H C).2 hC

theorem thompsonJ_map_eq (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    thompsonJ (H.map f) = (thompsonJ H).map f := by
  unfold thompsonJ
  rw [Subgroup.map_iSup]
  simp only [Subgroup.map_iSup]
  refine le_antisymm (iSup₂_le fun D hD => ?_) (iSup₂_le fun C hC => ?_)
  · obtain ⟨C, hC, rfl⟩ := (isMaxElemAbelian_map_iff_exists f hf H D).1 hD
    exact le_iSup₂_of_le C hC le_rfl
  · exact le_iSup₂_of_le (C.map f) ((isMaxElemAbelian_map_iff f hf H C).2 hC) le_rfl

theorem conjClosure_map_eq (f : A →* B) (V H : Subgroup A) :
    conjClosure (V.map f) (H.map f) = (conjClosure V H).map f := by
  unfold conjClosure
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨h * z * h⁻¹, ⟨h, hh, z, hz, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨h, hh, z, hz, rfl⟩, rfl⟩
    exact ⟨f h, ⟨h, hh, rfl⟩, f z, ⟨z, hz, rfl⟩, by simp⟩

theorem centerOf_map_eq (f : A →* B) (hf : Function.Injective f) (K : Subgroup A) :
    centerOf (K.map f) = (centerOf K).map f :=
  (map_inf_centralizer_eq f hf K K).symm

theorem relIndex_map_eq (f : A →* B) (hf : Function.Injective f) (K L : Subgroup A) :
    (K.map f).relIndex (L.map f) = K.relIndex L :=
  Subgroup.relIndex_map_map_of_injective K L hf

theorem twoResidual_map_eq (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    twoResidual (H.map f) = (twoResidual H).map f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hxH, rfl⟩ : y ∈ H.map f := twoResidual_le _ hy
    refine ⟨x, mem_twoResidual_iff.2 fun N hNH hHN hpow => ?_, rfl⟩
    refine (Subgroup.mem_map_iff_mem hf).1
      (mem_twoResidual_iff.1 hy (N.map f) (Subgroup.map_mono hNH)
        ((le_normalizer_map_iff f hf H N).2 hHN) ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := hpow z hz
    exact ⟨k, by rw [← map_pow]; exact ⟨_, hk, rfl⟩⟩
  · rintro ⟨x, hx, rfl⟩
    rw [mem_twoResidual_iff]
    intro N' hN'H hHN' hpow
    obtain ⟨N, rfl⟩ := exists_map_eq_of_le_map f hN'H
    refine ⟨x, ?_, rfl⟩
    refine mem_twoResidual_iff.1 hx N ((Subgroup.map_le_map_iff_of_injective hf).1 hN'H)
      ((le_normalizer_map_iff f hf H N).1 hHN') (fun z hz => ?_)
    obtain ⟨k, hk⟩ := hpow (f z) ⟨z, hz, rfl⟩
    exact ⟨k, (Subgroup.mem_map_iff_mem hf).1 (by rwa [← map_pow] at hk)⟩

private theorem mem_twoPrimeResidual_iff {H : Subgroup A} {x : A} :
    x ∈ twoPrimeResidual H ↔ ∀ N : Subgroup A, N ≤ H → H ≤ Subgroup.normalizer (N : Set A) →
      ¬ 2 ∣ N.relIndex H → x ∈ N := by
  unfold twoPrimeResidual
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h N h1 h2 h3
    exact h N ⟨h1, h2, h3⟩
  · rintro h N ⟨h1, h2, h3⟩
    exact h N h1 h2 h3

private theorem twoPrimeResidual_le (H : Subgroup A) : twoPrimeResidual H ≤ H := fun _ hx =>
  mem_twoPrimeResidual_iff.1 hx H le_rfl Subgroup.le_normalizer (by simp)

theorem twoPrimeResidual_map_eq (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    twoPrimeResidual (H.map f) = (twoPrimeResidual H).map f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hxH, rfl⟩ : y ∈ H.map f := twoPrimeResidual_le _ hy
    refine ⟨x, mem_twoPrimeResidual_iff.2 fun N hNH hHN hodd => ?_, rfl⟩
    refine (Subgroup.mem_map_iff_mem hf).1
      (mem_twoPrimeResidual_iff.1 hy (N.map f) (Subgroup.map_mono hNH)
        ((le_normalizer_map_iff f hf H N).2 hHN) ?_)
    rwa [relIndex_map_eq f hf]
  · rintro ⟨x, hx, rfl⟩
    rw [mem_twoPrimeResidual_iff]
    intro N' hN'H hHN' hodd
    obtain ⟨N, rfl⟩ := exists_map_eq_of_le_map f hN'H
    refine ⟨x, ?_, rfl⟩
    exact mem_twoPrimeResidual_iff.1 hx N ((Subgroup.map_le_map_iff_of_injective hf).1 hN'H)
      ((le_normalizer_map_iff f hf H N).1 hHN') (by rwa [relIndex_map_eq f hf] at hodd)

theorem isNormalIn_map_iff (f : A →* B) (hf : Function.Injective f) (H U N : Subgroup A) :
    IsNormalIn (H.map f) (U.map f) (N.map f) ↔ IsNormalIn H U N := by
  unfold IsNormalIn
  rw [Subgroup.map_le_map_iff_of_injective hf]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h g hg x hx
    have h1 := h (f g) ⟨g, hg, rfl⟩ (f x) ⟨x, hx, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact (Subgroup.mem_map_iff_mem hf).1 h1
  · rintro h _ ⟨g, hg, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨g * x * g⁻¹, h g hg x hx, rfl⟩

theorem isChiefStep_map_iff (f : A →* B) (hf : Function.Injective f) (H U L N : Subgroup A) :
    IsChiefStep (H.map f) (U.map f) (L.map f) (N.map f) ↔ IsChiefStep H U L N := by
  unfold IsChiefStep
  rw [isNormalIn_map_iff f hf, isNormalIn_map_iff f hf, Subgroup.map_lt_map_iff_of_injective hf]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h K hK hLK hKN
    rcases h (K.map f) ((isNormalIn_map_iff f hf H U K).2 hK) (Subgroup.map_mono hLK)
        (Subgroup.map_mono hKN) with h1 | h1
    · exact Or.inl (Subgroup.map_injective hf h1)
    · exact Or.inr (Subgroup.map_injective hf h1)
  · intro h K' hK' hLK hKN
    obtain ⟨K, rfl⟩ := exists_map_eq_of_le_map f hK'.1
    rw [isNormalIn_map_iff f hf] at hK'
    rcases h K hK' ((Subgroup.map_le_map_iff_of_injective hf).1 hLK)
        ((Subgroup.map_le_map_iff_of_injective hf).1 hKN) with h1 | h1
    · exact Or.inl (by rw [h1])
    · exact Or.inr (by rw [h1])

theorem isCentralStep_map_iff (f : A →* B) (hf : Function.Injective f) (H L N : Subgroup A) :
    IsCentralStep (H.map f) (L.map f) (N.map f) ↔ IsCentralStep H L N := by
  unfold IsCentralStep
  constructor
  · intro h g hg x hx
    have h1 := h (f g) ⟨g, hg, rfl⟩ (f x) ⟨x, hx, rfl⟩
    simp only [← map_inv, ← map_mul] at h1
    exact (Subgroup.mem_map_iff_mem hf).1 h1
  · rintro h _ ⟨g, hg, rfl⟩ _ ⟨x, hx, rfl⟩
    simp only [← map_inv, ← map_mul]
    exact ⟨_, h g hg x hx, rfl⟩

theorem exists_isChiefSeriesFrom_of_map (f : A →* B) (hf : Function.Injective f)
    (H U : Subgroup A) {N' : Subgroup B} {c : ℕ}
    (h : IsChiefSeriesFrom (H.map f) (U.map f) N' c) :
    ∃ N : Subgroup A, N.map f = N' ∧ IsChiefSeriesFrom H U N c := by
  induction h with
  | bot => exact ⟨⊥, Subgroup.map_bot f, IsChiefSeriesFrom.bot⟩
  | @central N₁ L₁ n hstep hcen _ ih =>
    obtain ⟨L, rfl, hL⟩ := ih
    obtain ⟨N, rfl⟩ := exists_map_eq_of_le_map f hstep.1.1
    exact ⟨N, rfl, IsChiefSeriesFrom.central ((isChiefStep_map_iff f hf H U L N).1 hstep)
      ((isCentralStep_map_iff f hf H L N).1 hcen) hL⟩
  | @noncentral N₁ L₁ n hstep hcen _ ih =>
    obtain ⟨L, rfl, hL⟩ := ih
    obtain ⟨N, rfl⟩ := exists_map_eq_of_le_map f hstep.1.1
    exact ⟨N, rfl, IsChiefSeriesFrom.noncentral ((isChiefStep_map_iff f hf H U L N).1 hstep)
      (fun hc => hcen ((isCentralStep_map_iff f hf H L N).2 hc)) hL⟩

theorem isChiefSeriesFrom_map_iff (f : A →* B) (hf : Function.Injective f)
    (H U N : Subgroup A) (c : ℕ) :
    IsChiefSeriesFrom (H.map f) (U.map f) (N.map f) c ↔ IsChiefSeriesFrom H U N c := by
  constructor
  · intro h
    obtain ⟨N₀, hN₀, h₀⟩ := exists_isChiefSeriesFrom_of_map f hf H U h
    rwa [← Subgroup.map_injective hf hN₀]
  · intro h
    induction h with
    | bot => rw [Subgroup.map_bot]; exact IsChiefSeriesFrom.bot
    | @central N L n hstep hcen _ ih =>
      exact IsChiefSeriesFrom.central ((isChiefStep_map_iff f hf H U L N).2 hstep)
        ((isCentralStep_map_iff f hf H L N).2 hcen) ih
    | @noncentral N L n hstep hcen _ ih =>
      exact IsChiefSeriesFrom.noncentral ((isChiefStep_map_iff f hf H U L N).2 hstep)
        (fun hc => hcen ((isCentralStep_map_iff f hf H L N).1 hc)) ih

theorem isSylowTwoOf_map_iff (f : A →* B) (hf : Function.Injective f) (S H : Subgroup A) :
    IsSylowTwoOf (S.map f) (H.map f) ↔ IsSylowTwoOf S H := by
  unfold IsSylowTwoOf
  rw [Subgroup.map_le_map_iff_of_injective hf, isPGroup_map_iff f hf]
  have h : ((S.map f).subgroupOf (H.map f)).index = (S.subgroupOf H).index :=
    relIndex_map_eq f hf S H
  rw [h]

theorem exists_isSylowTwoOf_of_map (f : A →* B) (hf : Function.Injective f) (H : Subgroup A)
    {S' : Subgroup B} (h : IsSylowTwoOf S' (H.map f)) :
    ∃ S : Subgroup A, S.map f = S' ∧ IsSylowTwoOf S H := by
  obtain ⟨S, rfl⟩ := exists_map_eq_of_le_map f h.1
  exact ⟨S, rfl, (isSylowTwoOf_map_iff f hf S H).1 h⟩

theorem isMaxSubgroupIn_map_iff (f : A →* B) (hf : Function.Injective f) (H N : Subgroup A) :
    IsMaxSubgroupIn (H.map f) (N.map f) ↔ IsMaxSubgroupIn H N := by
  unfold IsMaxSubgroupIn
  rw [Subgroup.map_lt_map_iff_of_injective hf]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h K hNK hKH
    exact Subgroup.map_injective hf
      (h (K.map f) ((Subgroup.map_lt_map_iff_of_injective hf).2 hNK) (Subgroup.map_mono hKH))
  · intro h K' hNK hKH
    obtain ⟨K, rfl⟩ := exists_map_eq_of_le_map f hKH
    rw [Subgroup.map_lt_map_iff_of_injective hf] at hNK
    rw [h K hNK ((Subgroup.map_le_map_iff_of_injective hf).1 hKH)]

theorem maxOver_map_eq (f : A →* B) (hf : Function.Injective f) (H X : Subgroup A) :
    maxOver (H.map f) (X.map f) = Subgroup.map f '' maxOver H X := by
  ext N'
  constructor
  · rintro ⟨hmax, hX⟩
    obtain ⟨N, rfl⟩ := exists_map_eq_of_le_map f hmax.1.le
    exact ⟨N, ⟨(isMaxSubgroupIn_map_iff f hf H N).1 hmax,
      (Subgroup.map_le_map_iff_of_injective hf).1 hX⟩, rfl⟩
  · rintro ⟨N, ⟨hmax, hX⟩, rfl⟩
    exact ⟨(isMaxSubgroupIn_map_iff f hf H N).2 hmax, Subgroup.map_mono hX⟩

theorem isUniqueMaxOver_map_iff (f : A →* B) (hf : Function.Injective f) (H T M : Subgroup A) :
    IsUniqueMaxOver (H.map f) (T.map f) (M.map f) ↔ IsUniqueMaxOver H T M := by
  unfold IsUniqueMaxOver
  rw [maxOver_map_eq f hf, ← Set.image_singleton,
    (Subgroup.map_injective hf).image_injective.eq_iff]

theorem mem_uFam_map_iff (f : A →* B) (hf : Function.Injective f) (H P X : Subgroup A) :
    P.map f ∈ uFam (H.map f) (X.map f) ↔ P ∈ uFam H X := by
  simp only [uFam, Set.mem_setOf_eq]
  rw [Subgroup.map_le_map_iff_of_injective hf, Subgroup.map_lt_map_iff_of_injective hf,
    maxOver_map_eq f hf, Set.ncard_image_of_injective _ (Subgroup.map_injective hf)]

theorem mem_uFamHat_map_iff (f : A →* B) (hf : Function.Injective f) (H P X : Subgroup A) :
    P.map f ∈ uFamHat (H.map f) (X.map f) ↔ P ∈ uFamHat H X := by
  simp only [uFamHat, Set.mem_setOf_eq]
  rw [mem_uFam_map_iff f hf, le_normalizer_map_iff f hf]

theorem isMinParabolicOf_map_iff (f : A →* B) (hf : Function.Injective f) (H P : Subgroup A) :
    IsMinParabolicOf (H.map f) (P.map f) ↔ IsMinParabolicOf H P := by
  constructor
  · rintro ⟨T', hT', hP⟩
    obtain ⟨T, rfl, hT⟩ := exists_isSylowTwoOf_of_map f hf H hT'
    exact ⟨T, hT, (mem_uFamHat_map_iff f hf H P T).1 hP⟩
  · rintro ⟨T, hT, hP⟩
    exact ⟨T.map f, (isSylowTwoOf_map_iff f hf T H).2 hT, (mem_uFamHat_map_iff f hf H P T).2 hP⟩

theorem charTwo_map_iff (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    CharTwo (H.map f) ↔ CharTwo H := by
  unfold CharTwo
  rw [pCoreOf_map_eq f hf, ← map_inf_centralizer_eq f hf,
    Subgroup.map_le_map_iff_of_injective hf]

theorem isSolvable_map_iff (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    Group.IsSolvable ↥(H.map f) ↔ Group.IsSolvable ↥H := by
  let e : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
  constructor
  · intro h
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · intro h
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

end General

section Iso

variable {X Y : Type*} [Group X] [Group Y]

theorem exists_isElementaryAbelian_of_injective (g : X →* Y) (hg : Function.Injective g)
    (p r : ℕ) (h : ∃ E : Subgroup X, IsElementaryAbelian p E ∧ Nat.card E = p ^ r) :
    ∃ E : Subgroup Y, IsElementaryAbelian p E ∧ Nat.card E = p ^ r := by
  obtain ⟨E, hE, hcard⟩ := h
  exact ⟨E.map g, hE.subgroup_map g, by rw [Subgroup.card_map_of_injective hg, hcard]⟩

theorem pRank_eq_of_mulEquiv (e : X ≃* Y) (p : ℕ) : CFSG.pRank p X = CFSG.pRank p Y := by
  unfold CFSG.pRank
  congr 1
  ext r
  exact ⟨exists_isElementaryAbelian_of_injective e.toMonoidHom e.injective p r,
    exists_isElementaryAbelian_of_injective e.symm.toMonoidHom e.symm.injective p r⟩

theorem isStronglyQuasithin_congr (e : X ≃* Y) :
    CFSG.IsStronglyQuasithin X ↔ CFSG.IsStronglyQuasithin Y := by
  unfold CFSG.IsStronglyQuasithin
  simp only [pRank_eq_of_mulEquiv e]

end Iso

section SQTK

theorem isSQTKCat_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    CFSG.SectionRank.IsSQTKCat X ↔ CFSG.SectionRank.IsSQTKCat Y :=
  and_congr (isStronglyQuasithin_congr e) ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isSQTKCat_map_iff {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (H : Subgroup A) :
    CFSG.SectionRank.IsSQTKCat ↥(H.map f) ↔ CFSG.SectionRank.IsSQTKCat ↥H :=
  (isSQTKCat_congr (H.equivMapOfInjective f hf)).symm

end SQTK

end CFSG.Quasithin.SimsD1.TransGrp
