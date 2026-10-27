module

public import CFSG.LieType.TitsSimplicity.Core
public import CFSG.LieType.Steinberg.CentralExt.BorelIndex
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerBorel

public section

namespace CFSG.StandardType.SteinbergAut

open CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity
open scoped commutatorElement

theorem steinbergAut_neg_single_mem_roots {K : Type*} [Group K] {D : UniversalRootDatum K}
    (i : Fin D.rank) :
    -Pi.single i 1 ∈ D.roots := by
  have := weylAction_mem_roots D.isFiniteType
    ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i)
    ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
  rwa [weylAction_simple_single] at this

theorem mem_normalizer_of_mem_H {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {k : Fin D.rank} {h : K} (hh : h ∈ H k) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    h ∈ Subgroup.normalizer (D.rootGroup γ : Set K) := by
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨hct.H_conj_mem k γ hγ h hh x, fun hx => ?_⟩
  have := hct.H_conj_mem k γ hγ h⁻¹ (inv_mem hh) _ hx
  simpa [mul_assoc] using this

theorem n_notMem_normalizer {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank) {S : Subgroup K}
    (hS : S ⊓ negUnipotent D = ⊥) (hX : D.rootGroup (Pi.single i 1) ≤ S) :
    n i ∉ Subgroup.normalizer (S : Set K) := by
  intro hn
  have hsi := (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  apply hext.ne_bot _ hsi
  rw [eq_bot_iff]
  intro x hx
  have h1 : n i * x * (n i)⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hn x).1 (hX hx)
  have h2 : n i * x * (n i)⁻¹ ∈ negUnipotent D := by
    have := (actsAs_n hct i).conj_mem hsi hx
    rw [weylAction_simple_single] at this
    exact rootGroup_le_negUnipotent (steinbergAut_neg_single_mem_roots i)
      (by rw [ht_neg, ht_single]; exact neg_one_lt_zero) this
  have h3 : n i * x * (n i)⁻¹ = 1 := by
    have : n i * x * (n i)⁻¹ ∈ S ⊓ negUnipotent D := ⟨h1, h2⟩
    rwa [hS, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  have : x = (n i)⁻¹ * (n i * x * (n i)⁻¹) * n i := by group
  rw [this, h3]; group

theorem normalizer_posUnipotent {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) :
    Subgroup.normalizer (posUnipotent D : Set K) = borel D H := by
  refine le_antisymm (le_borel_of_forall_n_notMem hct hext
    (borel_le_normalizer_posUnipotent hct) fun i => ?_) (borel_le_normalizer_posUnipotent hct)
  exact n_notMem_normalizer hct hext i (posUnipotent_inf_negUnipotent hext)
    (rootGroup_le_posUnipotent ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
      (ht_single_pos i))

theorem steinbergAut_not_le_centralizer {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    ¬ D.rootGroup (-Pi.single i 1) ≤
      Subgroup.centralizer (D.rootGroup (Pi.single i 1) : Set K) := by
  intro hc
  have hsi := (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hle : rankOne D.rootGroup i ≤
      Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K) :=
    sup_le (Subgroup.le_normalizer) (hc.trans (Subgroup.centralizer_le_normalizer _))
  refine n_notMem_normalizer hct hext i ?_ le_rfl (hle (hct.n_mem i))
  exact eq_bot_iff.2 ((inf_le_inf_right _ (rootGroup_le_posUnipotent hsi (ht_single_pos i))).trans
    (posUnipotent_inf_negUnipotent hext).le)

theorem mem_H_of_mem_rankOne {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank) {y : K} (hy : y ∈ rankOne D.rootGroup i)
    (h₁ : y ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K))
    (h₂ : y ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K)) : y ∈ H i := by
  have hsi := (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  rcases hext.rankOne_bruhat i y hy with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
  · have hun : u ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) := by
      have e : u = h⁻¹ * (h * u) := by group
      rw [e]
      exact mul_mem
        (inv_mem (mem_normalizer_of_mem_H hct hh (steinbergAut_neg_single_mem_roots i))) h₂
    rw [hext.eq_one_of_mem_normalizer i u hu hun, mul_one]
    exact hh
  · exfalso
    have hXn : ∀ z ∈ D.rootGroup (Pi.single i 1),
        z ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K) :=
      fun z hz => Subgroup.le_normalizer hz
    have hn : n i ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K) := by
      have e : n i = u⁻¹ * (u * n i * h * v) * v⁻¹ * h⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (mul_mem (inv_mem (hXn u hu)) h₁) (inv_mem (hXn v hv)))
        (inv_mem (mem_normalizer_of_mem_H hct hh hsi))
    refine n_notMem_normalizer hct hext i ?_ le_rfl hn
    exact eq_bot_iff.2 ((inf_le_inf_right _ (rootGroup_le_posUnipotent hsi (ht_single_pos i))).trans
      (posUnipotent_inf_negUnipotent hext).le)

theorem le_posUnipotent_of_isPGroup {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) [Finite K]
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup K)))
    {P : Subgroup K} (hP : IsPGroup 2 P) (hPB : P ≤ borel D H) : P ≤ posUnipotent D := by
  intro x hx
  obtain ⟨a, ha⟩ := hP ⟨x, hx⟩
  have hxa : x ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hxB := hPB hx
  have hle : posUnipotent D ≤ borel D H := posUnipotent_le_borel
  haveI hN : ((posUnipotent D).subgroupOf (borel D H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 (borel_le_normalizer_posUnipotent hct)
  have hcardN : Nat.card ((posUnipotent D).subgroupOf (borel D H)) = Nat.card (posUnipotent D) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hcard : Nat.card (borel D H ⧸ (posUnipotent D).subgroupOf (borel D H)) =
      Nat.card (⨆ i, H i : Subgroup K) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((posUnipotent D).subgroupOf (borel D H))
    rw [hcardN, CentralExt.BorelIndex.card_borel hct hext] at h1
    have hpos : 0 < Nat.card (posUnipotent D) := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  set y : borel D H ⧸ (posUnipotent D).subgroupOf (borel D H) := QuotientGroup.mk ⟨x, hxB⟩
  have hy : y ^ 2 ^ a = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hxB⟩ : borel D H) ^ 2 ^ a = 1 := Subtype.ext (by simpa using hxa)
    rw [this, QuotientGroup.mk_one]
  have h1 : orderOf y ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hy
  have h2 : orderOf y ∣ Nat.card (⨆ i, H i : Subgroup K) := hcard ▸ orderOf_dvd_natCard y
  have hy1 : y = 1 := orderOf_eq_one_iff.1
    (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left a hT) h1 h2)
  have := (QuotientGroup.eq_one_iff _).1 hy1
  exact Subgroup.mem_subgroupOf.1 this

theorem steinbergAut_le_of_isPGroup_of_le_sup {K : Type*} [Group K] [Finite K] {Z₀ X Y : Subgroup K}
    (hZ : Z₀ ≤ Subgroup.center K)
    (hZodd : Nat.Coprime 2 (Nat.card Z₀)) (hX : IsPGroup 2 X) (hY : IsPGroup 2 Y)
    (h : Y ≤ X ⊔ Z₀) : Y ≤ X := by
  have hZn : Z₀.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.1 (hZ hz) g, mul_inv_cancel_right]; exact hz⟩
  intro y hy
  have hy' : y ∈ ((X ⊔ Z₀ : Subgroup K) : Set K) := h hy
  rw [Subgroup.mul_normal] at hy'
  obtain ⟨x, hx, z, hz, rfl⟩ := Set.mem_mul.1 hy'
  obtain ⟨a, ha⟩ := hX ⟨x, hx⟩
  obtain ⟨b, hb⟩ := hY ⟨x * z, hy⟩
  have ha' : x ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hb' : (x * z) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hcomm : Commute x z := Subgroup.mem_center_iff.1 (hZ hz) x
  have hz1 : z ^ 2 ^ (a + b) = 1 := by
    have e : (x * z) ^ 2 ^ (a + b) = x ^ 2 ^ (a + b) * z ^ 2 ^ (a + b) := hcomm.mul_pow _
    have hxab : x ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, ha', one_pow]
    have hyab : (x * z) ^ 2 ^ (a + b) = 1 := by
      rw [pow_add, mul_comm (2 ^ a), pow_mul, hb', one_pow]
    rw [hxab, hyab, one_mul] at e
    exact e.symm
  have hord : orderOf z = 1 := by
    have h1 : orderOf z ∣ 2 ^ (a + b) := orderOf_dvd_of_pow_eq_one hz1
    have h2 : orderOf z ∣ Nat.card Z₀ := by
      have := Subgroup.orderOf_dvd_natCard Z₀ hz
      exact this
    have hcop : Nat.Coprime (2 ^ (a + b)) (Nat.card Z₀) := Nat.Coprime.pow_left _ hZodd
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff.1 hord, mul_one]
  exact hx

theorem steinbergAut_le_of_map_le {K : Type*} [Group K] [Finite K] {G : Type*} [Group G]
    (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) (hodd : Nat.Coprime 2 (Nat.card ψ.ker))
    {X Y : Subgroup K} (hX : IsPGroup 2 X) (hY : IsPGroup 2 Y) (h : Y.map ψ ≤ X.map ψ) :
    Y ≤ X := by
  refine steinbergAut_le_of_isPGroup_of_le_sup hker hodd hX hY ?_
  intro y hy
  obtain ⟨x, hx, e⟩ := h ⟨y, hy, rfl⟩
  have hk : x⁻¹ * y ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
  have : y = x * (x⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hx hk

theorem steinbergAut_map_inf_of_ker_le {K : Type*} [Group K] {G : Type*} [Group G] (ψ : K →* G)
    {P Q : Subgroup K} (h : ψ.ker ≤ P) : (P ⊓ Q).map ψ = P.map ψ ⊓ Q.map ψ := by
  refine le_antisymm (Subgroup.map_inf_le _ _ _) ?_
  rintro _ ⟨⟨p, hp, rfl⟩, ⟨q, hq, hpq⟩⟩
  have hk : p⁻¹ * q ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpq, inv_mul_cancel]
  have hqP : q ∈ P := by
    have := mul_mem hp (h hk)
    rwa [mul_inv_cancel_left] at this
  exact ⟨q, ⟨hqP, hq⟩, hpq⟩

theorem nrep_conj_mem_posUnipotent_of_forall_isRightDescent {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀ i) {u : K}
    (hu : u ∈ negUnipotent D) :
    nrep hct w₀ * u * (nrep hct w₀)⁻¹ ∈ posUnipotent D :=
  conj_mem_of_forall_mem (fun _ hγ _ hy => rootGroup_le_posUnipotent
    (weylAction_mem_roots _ w₀ hγ.1) (by
      have h := ht_weylAction_neg hw₀ (OfCartan.neg_mem_roots D.isFiniteType hγ.1)
        (by rw [ht_neg]; linarith [hγ.2])
      rw [map_neg, ht_neg] at h
      linarith)
    ((actsAs_nrep hct w₀).conj_mem hγ.1 hy)) hu

theorem steinbergAut_card_map_conj {K : Type*} [Group K] (S : Subgroup K) (g : K) :
    Nat.card (S.map (MulAut.conj g).toMonoidHom) = Nat.card S :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem map_conj_nrep_posUnipotent {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    [Finite K] {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀ i) :
    (posUnipotent D).map (MulAut.conj (nrep hct w₀)).toMonoidHom = negUnipotent D := by
  have h1 : (posUnipotent D).map (MulAut.conj (nrep hct w₀)).toMonoidHom ≤ negUnipotent D := by
    rintro _ ⟨u, hu, rfl⟩
    exact nrep_conj_mem_negUnipotent_of_forall_isRightDescent hct hw₀ hu
  have h2 : (negUnipotent D).map (MulAut.conj (nrep hct w₀)).toMonoidHom ≤ posUnipotent D := by
    rintro _ ⟨u, hu, rfl⟩
    exact nrep_conj_mem_posUnipotent_of_forall_isRightDescent hct hw₀ hu
  refine Subgroup.eq_of_le_of_card_ge h1 ?_
  calc Nat.card (negUnipotent D) = _ := (steinbergAut_card_map_conj _ (nrep hct w₀)).symm
    _ ≤ Nat.card (posUnipotent D) := Subgroup.card_le_of_le h2
    _ = _ := (steinbergAut_card_map_conj _ _).symm

theorem map_conj_nrep_negUnipotent {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    [Finite K] {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀ i) :
    (negUnipotent D).map (MulAut.conj (nrep hct w₀)).toMonoidHom = posUnipotent D := by
  have h1 : (posUnipotent D).map (MulAut.conj (nrep hct w₀)).toMonoidHom ≤ negUnipotent D := by
    rintro _ ⟨u, hu, rfl⟩
    exact nrep_conj_mem_negUnipotent_of_forall_isRightDescent hct hw₀ hu
  have h2 : (negUnipotent D).map (MulAut.conj (nrep hct w₀)).toMonoidHom ≤ posUnipotent D := by
    rintro _ ⟨u, hu, rfl⟩
    exact nrep_conj_mem_posUnipotent_of_forall_isRightDescent hct hw₀ hu
  refine Subgroup.eq_of_le_of_card_ge h2 ?_
  calc Nat.card (posUnipotent D) = _ := (steinbergAut_card_map_conj _ (nrep hct w₀)).symm
    _ ≤ Nat.card (negUnipotent D) := Subgroup.card_le_of_le h1
    _ = _ := (steinbergAut_card_map_conj _ _).symm

theorem mem_negUnipotent_iff {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    [Finite K] {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀ i) (y : K) :
    y ∈ negUnipotent D ↔ (nrep hct w₀)⁻¹ * y * nrep hct w₀ ∈ posUnipotent D := by
  rw [← map_conj_nrep_posUnipotent hct hw₀]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [mul_assoc] using hu
  · exact fun h => ⟨_, h, by simp [mul_assoc]⟩

theorem normalizer_negUnipotent {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) [Finite K] {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀ i) :
    Subgroup.normalizer (negUnipotent D : Set K) =
      (borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom := by
  ext g
  have e2 : g ∈ (borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom ↔
      (nrep hct w₀)⁻¹ * g * nrep hct w₀ ∈ borel D H := by
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa [mul_assoc] using hb
    · exact fun h => ⟨_, h, by simp [mul_assoc]⟩
  rw [e2, ← normalizer_posUnipotent hct hext, Subgroup.mem_normalizer_iff,
    Subgroup.mem_normalizer_iff]
  constructor
  · intro hg y
    have := hg (nrep hct w₀ * y * (nrep hct w₀)⁻¹)
    rw [mem_negUnipotent_iff hct hw₀, mem_negUnipotent_iff hct hw₀] at this
    convert this using 2 <;> group
  · intro hg x
    have := hg ((nrep hct w₀)⁻¹ * x * nrep hct w₀)
    rw [mem_negUnipotent_iff hct hw₀, mem_negUnipotent_iff hct hw₀]
    convert this using 2 <;> group

theorem borel_inf_negBorel {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hBU : BruhatExtras D H) [Finite K] {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀ i) :
    borel D H ⊓ (borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom =
      (⨆ i, H i : Subgroup K) := by
  refine le_antisymm ?_ (le_inf iSup_le_borel ?_)
  · rintro b ⟨hb, b', hb', hbb'⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hbb'
    have hb2 : b ∈ (borel D H : Set K) := hb
    rw [coe_borel hct, Set.mem_mul] at hb2
    obtain ⟨t, ht, u, hu, rfl⟩ := hb2
    have hv : (nrep hct w₀)⁻¹ * u * (nrep hct w₀) ∈ borel D H ⊓ negUnipotent D := by
      refine ⟨?_, ?_⟩
      · have e : (nrep hct w₀)⁻¹ * u * (nrep hct w₀) =
            ((nrep hct w₀)⁻¹ * t⁻¹ * (nrep hct w₀)) * b' := by
          have : u = t⁻¹ * ((nrep hct w₀) * b' * (nrep hct w₀)⁻¹) := by rw [hbb']; group
          rw [this]; group
        rw [e]
        refine mul_mem (iSup_le_borel ?_) hb'
        have := conj_mem_iSup_of_mem_weylN hct (inv_mem (nrep_mem_weylN hct w₀)) (inv_mem ht)
        simpa using this
      · have := (map_conj_nrep_negUnipotent hct hw₀).symm ▸ hu
        obtain ⟨v, hv, e⟩ := this
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
        rw [← e]
        convert hv using 1
        group
    rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at hv
    have hu1 : u = 1 := by
      have : u = (nrep hct w₀) * ((nrep hct w₀)⁻¹ * u * (nrep hct w₀)) * (nrep hct w₀)⁻¹ := by
        group
      rw [this, hv]; group
    rw [hu1, mul_one]
    exact ht
  · intro t ht
    refine ⟨(nrep hct w₀)⁻¹ * t * (nrep hct w₀), iSup_le_borel ?_, by simp [mul_assoc]⟩
    have := conj_mem_iSup_of_mem_weylN hct (inv_mem (nrep_mem_weylN hct w₀)) ht
    simpa using this

theorem ggTorus_eq_iSup {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) [Finite K] :
    ggTorus D = (⨆ i, H i : Subgroup K) := by
  refine le_antisymm ?_ (le_iInf₂ fun γ hγ => iSup_le_normalizer_rootGroup hct hγ)
  intro h hh
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  have hN : ∀ γ ∈ D.roots, h ∈ Subgroup.normalizer (D.rootGroup γ : Set K) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    exact hh
  have hh' : (nrep hct w₀)⁻¹ * h * nrep hct w₀ ∈ ggTorus D := by
    simp only [ggTorus, Subgroup.mem_iInf]
    intro γ hγ
    have hA := actsAs_nrep hct w₀
    have hγ' := weylAction_mem_roots _ w₀ hγ
    have e1 : ∀ y, y ∈ D.rootGroup γ ↔ nrep hct w₀ * y * (nrep hct w₀)⁻¹ ∈
        D.rootGroup (weylAction D.isFiniteType w₀ γ) := fun y =>
      ⟨fun hy => hA.conj_mem hγ hy, fun hy => by
        have := hA.inv_conj_mem hγ' hy
        rw [weylAction_inv_apply_apply] at this
        simpa [mul_assoc] using this⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [e1, Subgroup.mem_normalizer_iff.1 (hN _ hγ'), e1]
    constructor <;> intro hx <;> convert hx using 1 <;> group
  have hmem : h ∈ borel D H ⊓ (borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom :=
    ⟨PsiDiag.mem_borel_of_mem_ggTorus hct hext hh,
      ⟨_, PsiDiag.mem_borel_of_mem_ggTorus hct hext hh', by simp [mul_assoc]⟩⟩
  rwa [borel_inf_negBorel hct hBU hw₀] at hmem

theorem steinbergAut_map_conj_mul' {K : Type*} [Group K] (S : Subgroup K) (a b : K) :
    S.map (MulAut.conj (a * b)).toMonoidHom =
      (S.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem steinbergAut_map_conj_of_mem_normalizer {K : Type*} [Group K] {S : Subgroup K} {g : K}
    (hg : g ∈ Subgroup.normalizer (S : Set K)) : S.map (MulAut.conj g).toMonoidHom = S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).1 hx
    simpa using this

theorem steinbergAut_iSup_le_normalizer_negUnipotent {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) :
    (⨆ i, H i : Subgroup K) ≤ Subgroup.normalizer (negUnipotent D : Set K) :=
  le_normalizer_iSup₂ fun t ht γ hγ y hy =>
    rootGroup_le_negUnipotent hγ.1 hγ.2
      ((Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_rootGroup hct hγ.1 ht) y).1 hy)

theorem exists_eq_map_conj_negUnipotent {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) [Finite K]
    {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {k : K}
    (h : ((posUnipotent D).map (MulAut.conj k).toMonoidHom).map ψ ⊓ (posUnipotent D).map ψ = ⊥) :
    ∃ v ∈ posUnipotent D, (posUnipotent D).map (MulAut.conj k).toMonoidHom =
      (negUnipotent D).map (MulAut.conj v).toMonoidHom := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_bruhatCell hct hext k
  have hZT : Subgroup.center K ≤ (⨆ i, H i : Subgroup K) := by
    rw [center_eq_normalCore_borel hct hext hBU]
    exact normalCore_borel_le_iSup hct hBU
  have hneg : ∀ γ ∈ D.roots, 0 < ht γ → ht (weylAction D.isFiniteType w γ) < 0 := by
    intro γ hγ hγp
    by_contra hc
    have hδ := weylAction_mem_roots _ w hγ
    have hδp : 0 < ht (weylAction D.isFiniteType w γ) := by
      rcases nonneg_or_nonpos D.isFiniteType D.divisible hδ with h' | h'
      · exact ht_pos_of_nonneg hδ h'
      · exact absurd (ht_neg_of_nonpos hδ h') hc
    apply hext.ne_bot _ hδ
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hz1 : b₁ * x * b₁⁻¹ ∈ posUnipotent D :=
      (Subgroup.mem_normalizer_iff.1 (borel_le_normalizer_posUnipotent hct hb₁) x).1
        (rootGroup_le_posUnipotent hδ hδp hx)
    have hz2 : b₁ * x * b₁⁻¹ ∈
        (posUnipotent D).map (MulAut.conj (b₁ * nrep hct w * b₂)).toMonoidHom := by
      have hy := (actsAs_nrep hct w).inv_conj_mem hδ hx
      rw [weylAction_inv_apply_apply] at hy
      have hu : b₂⁻¹ * ((nrep hct w)⁻¹ * x * nrep hct w) * b₂ ∈ posUnipotent D := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem (borel_le_normalizer_posUnipotent hct hb₂))
          _).1 (rootGroup_le_posUnipotent hγ hγp hy)
        simpa using this
      exact ⟨_, hu, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    have hψ : ψ (b₁ * x * b₁⁻¹) = 1 := by
      have : ψ (b₁ * x * b₁⁻¹) ∈ (((posUnipotent D).map
          (MulAut.conj (b₁ * nrep hct w * b₂)).toMonoidHom).map ψ ⊓ (posUnipotent D).map ψ) :=
        ⟨⟨_, hz2, rfl⟩, ⟨_, hz1, rfl⟩⟩
      rwa [h, Subgroup.mem_bot] at this
    have hzT : b₁ * x * b₁⁻¹ ∈ (⨆ i, H i : Subgroup K) ⊓ posUnipotent D :=
      ⟨hZT (hker hψ), hz1⟩
    have h0 : (⨆ i, H i : Subgroup K) ⊓ posUnipotent D = ⊥ := hext.torus_inf_posPart
    rw [h0, Subgroup.mem_bot] at hzT
    have : x = b₁⁻¹ * (b₁ * x * b₁⁻¹) * b₁ := by group
    rw [this, hzT]
    group
  have hle : (posUnipotent D).map (MulAut.conj (nrep hct w)).toMonoidHom ≤ negUnipotent D := by
    rintro _ ⟨u, hu, rfl⟩
    exact conj_mem_of_forall_mem (fun γ hγ _ hy => rootGroup_le_negUnipotent
      (weylAction_mem_roots _ w hγ.1) (hneg γ hγ.1 hγ.2)
      ((actsAs_nrep hct w).conj_mem hγ.1 hy)) hu
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  have hcard : Nat.card (negUnipotent D) = Nat.card (posUnipotent D) := by
    rw [← map_conj_nrep_posUnipotent hct hw₀, steinbergAut_card_map_conj]
  have heq : (posUnipotent D).map (MulAut.conj (nrep hct w)).toMonoidHom = negUnipotent D :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, steinbergAut_card_map_conj])
  have hb₁' : b₁ ∈ (borel D H : Set K) := hb₁
  rw [coe_borel hct, Set.mem_mul] at hb₁'
  obtain ⟨t, ht, u, hu, rfl⟩ := hb₁'
  have hv : t * u * t⁻¹ ∈ posUnipotent D :=
    (Subgroup.mem_normalizer_iff.1 (borel_le_normalizer_posUnipotent hct (iSup_le_borel ht)) u).1 hu
  refine ⟨t * u * t⁻¹, hv, ?_⟩
  rw [steinbergAut_map_conj_mul', steinbergAut_map_conj_mul',
    steinbergAut_map_conj_of_mem_normalizer
    (borel_le_normalizer_posUnipotent hct hb₂), heq,
    show t * u = t * u * t⁻¹ * t by group, steinbergAut_map_conj_mul',
    steinbergAut_map_conj_of_mem_normalizer
      (steinbergAut_iSup_le_normalizer_negUnipotent hct ht), mul_inv_cancel_right]

theorem forall_isRightDescent_of_length_le {K : Type*} [Group K] {D : UniversalRootDatum K}
    {v : (coxeterMatrix D.isFiniteType).Group}
    (hv : ∀ w, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).length w ≤
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem).length v) :
    ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent v i := fun i => by
  by_contra hi
  have h := ((coxeterMatrix D.isFiniteType).toCoxeterSystem).not_isRightDescent_iff.mp hi
  have := hv (v * ((coxeterMatrix D.isFiniteType).toCoxeterSystem).simple i)
  omega

theorem notMem_negUnipotent_mul_n {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) [Finite K] (i : Fin D.rank) {b : K}
    (hb : b ∈ borel D H) :
    b * n i ∉ negUnipotent D := by
  intro hmem
  have := finite_group D.isFiniteType
  obtain ⟨w₀, hmax⟩ := Finite.exists_max fun w : (coxeterMatrix D.isFiniteType).Group =>
    ((coxeterMatrix D.isFiniteType).toCoxeterSystem).length w
  have hw₀ := forall_isRightDescent_of_length_le hmax
  have hL : ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsLeftDescent w₀ i := by
    rw [← CoxeterSystem.isRightDescent_inv_iff]
    exact forall_isRightDescent_of_length_le (fun w => by
      rw [((coxeterMatrix D.isFiniteType).toCoxeterSystem).length_inv]; exact hmax w) i
  have hnl : ¬ ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsLeftDescent
      (((coxeterMatrix D.isFiniteType).toCoxeterSystem).simple i * w₀) i := fun h => by
    have := hmax (((coxeterMatrix D.isFiniteType).toCoxeterSystem).simple i * w₀)
    unfold CoxeterSystem.IsLeftDescent at h
    rw [← mul_assoc, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).simple_mul_simple_self,
      one_mul] at h
    omega
  have hn₀ : nrep hct w₀ =
      n i * nrep hct (((coxeterMatrix D.isFiniteType).toCoxeterSystem).simple i * w₀) := by
    have := nrep_simple_mul hct hnl
    rwa [← mul_assoc, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).simple_mul_simple_self,
      one_mul] at this
  have h1 : b * n i * nrep hct w₀ ∈ bruhatCell hct w₀ := by
    have hu := (mem_negUnipotent_iff hct hw₀ _).1 hmem
    exact ⟨1, one_mem _, _, posUnipotent_le_borel hu, by group⟩
  have h2 : b * n i * nrep hct w₀ ∈ bruhatCell hct
      (((coxeterMatrix D.isFiniteType).toCoxeterSystem).simple i * w₀) := by
    rw [hn₀]
    exact ⟨b * n i ^ 2, mul_mem hb (iSup_le_borel (Subgroup.mem_iSup_of_mem i (hct.sq_mem i))),
      1, one_mem _, by simp only [pow_two, mul_one, mul_assoc]⟩
  have he := eq_of_mem_bruhatCell hct hext h1 h2
  unfold CoxeterSystem.IsLeftDescent at hL
  rw [← he] at hL
  exact lt_irrefl _ hL

@[expose] def negUnipotentExcept {K : Type*} [Group K] (D : UniversalRootDatum K)
    (i : Fin D.rank) : Subgroup K :=
  ⨆ γ ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).negExcept i, D.rootGroup γ

theorem rootGroup_le_negUnipotentExcept {K : Type*} [Group K] {D : UniversalRootDatum K}
    {i : Fin D.rank} {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).negExcept i) :
    D.rootGroup γ ≤ negUnipotentExcept D i :=
  le_iSup₂_of_le
    (f := fun γ (_ : γ ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).negExcept i) =>
      D.rootGroup γ)
    γ hγ le_rfl

theorem negUnipotentExcept_le_negUnipotent {K : Type*} [Group K] {D : UniversalRootDatum K}
    (i : Fin D.rank) :
    negUnipotentExcept D i ≤ negUnipotent D :=
  iSup₂_le fun _ hγ => rootGroup_le_negUnipotent hγ.1.1 hγ.1.2

theorem ht_neg_single_neg {K : Type*} [Group K] {D : UniversalRootDatum K} (i : Fin D.rank) :
    ht (-Pi.single i 1 : Fin D.rank → ℤ) < 0 := by
  rw [ht_neg, ht_single]
  exact neg_one_lt_zero

theorem negUnipotent_eq_sup {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    negUnipotent D = negUnipotentExcept D i ⊔ D.rootGroup (-Pi.single i 1) := by
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    by_cases h1 : γ = -Pi.single i 1
    · subst h1
      exact le_sup_right
    by_cases h2 : γ = -(2 • Pi.single i 1)
    · subst h2
      have := hext.two_smul_le _ (steinbergAut_neg_single_mem_roots i)
        (by rw [smul_neg]; exact hγ.1)
      rw [smul_neg] at this
      exact this.trans le_sup_right
    refine le_sup_of_le_left (rootGroup_le_negUnipotentExcept ⟨hγ, ?_⟩)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  · exact sup_le (negUnipotentExcept_le_negUnipotent i)
      (rootGroup_le_negUnipotent (steinbergAut_neg_single_mem_roots i) (ht_neg_single_neg i))

theorem rootGroup_neg_single_le_normalizer {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    D.rootGroup (-Pi.single i 1) ≤ Subgroup.normalizer (negUnipotentExcept D i : Set K) :=
  le_normalizer_iSup₂ fun x hx γ hγ y hy => by
    have hc := hext.commutator_mem _ (steinbergAut_neg_single_mem_roots i) γ hγ.1.1
      ((RootSystem.ofCartan D.isFiniteType D.divisible).linIndepPair_of_mem_negExcept
        (Or.inr rfl) hγ) x hx y hy
    have hle : ⨆ ε ∈ openCone D.roots (-Pi.single i 1) γ, D.rootGroup ε ≤
        negUnipotentExcept D i := iSup₂_le fun _ hε =>
      rootGroup_le_negUnipotentExcept
        ((RootSystem.ofCartan D.isFiniteType D.divisible).openCone_subset_negExcept
          (Or.inr rfl) hγ hε)
    have h : ⁅x, y⁆ * y ∈ negUnipotentExcept D i :=
      mul_mem (hle hc) (rootGroup_le_negUnipotentExcept hγ hy)
    rwa [commutatorElement_def, inv_mul_cancel_right] at h

theorem conj_n_mem_negUnipotentExcept {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (i : Fin D.rank) {u : K}
    (hu : u ∈ negUnipotentExcept D i) : n i * u * (n i)⁻¹ ∈ negUnipotentExcept D i :=
  conj_mem_of_forall_mem (P := (RootSystem.ofCartan D.isFiniteType D.divisible).negExcept i)
    (X := D.rootGroup) (fun γ hγ y hy => by
    have h := (actsAs_n hct i).conj_mem hγ.1.1 hy
    rw [weylAction_simple] at h
    exact rootGroup_le_negUnipotentExcept
      ((RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem_negExcept hγ) h) hu

theorem steinbergAut_inversionUnipotent_simple_le {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    inversionUnipotent D ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) ≤
      D.rootGroup (Pi.single i 1) := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hγr, h1, h2⟩ := hγ
  by_cases e1 : γ = Pi.single i 1
  · rw [e1]
  by_cases e2 : γ = 2 • Pi.single i 1
  · subst e2
    exact hext.two_smul_le _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) hγr
  exfalso
  have hpe : γ ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).posExcept i :=
    ⟨⟨hγr, h1⟩, by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨e1, e2⟩⟩
  have := ((RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem_posExcept hpe).1.2
  rw [weylAction_simple] at h2
  have h2' : ht ((RootSystem.ofCartan D.isFiniteType D.divisible).refl i γ) < 0 := h2
  omega

theorem mem_borel_or_mem_bruhatCell_of_mem_minParabolic {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank) {g : K}
    (hg : g ∈ borel D H ⊔ rankOne D.rootGroup i) :
    g ∈ borel D H ∨
      g ∈ bruhatCell hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) := by
  have hT3 : ∀ b ∈ borel D H,
      n i * b * n i ∈ borel D H ∨ n i * b * n i ∈
        bruhatCell hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) := by
    intro b hb
    have := n_mul_mul_nrep_mem hct hext
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) i hb
    rw [nrep_simple, CoxeterSystem.simple_mul_simple_self, bruhatCell_one] at this
    exact ((Set.mem_union _ _ _).1 this).symm
  have hsq : (n i ^ 2)⁻¹ ∈ borel D H := inv_mem (iSup_le_borel (sq_n_mem_iSup hct i))
  let S : Subgroup K :=
    { carrier := {g | g ∈ borel D H ∨
        g ∈ bruhatCell hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i)}
      one_mem' := Or.inl (one_mem _)
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (mul_mem ha hb)
        · exact Or.inr (mul_mem_bruhatCell hct ha hb)
        · exact Or.inr (mul_mem_bruhatCell_right hct ha hb)
        · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := ha
          obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := hb
          have e : b₁ * nrep hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) * b₂ *
                (b₃ * nrep hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) * b₄) =
              b₁ * (n i * (b₂ * b₃) * n i) * b₄ := by
            rw [nrep_simple]
            group
          change _ ∈ borel D H ∨ _ ∈
            bruhatCell hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i)
          rw [e]
          rcases hT3 _ (mul_mem hb₂ hb₃) with h | h
          · exact Or.inl (mul_mem (mul_mem hb₁ h) hb₄)
          · exact Or.inr (mul_mem_bruhatCell_right hct (mul_mem_bruhatCell hct hb₁ h) hb₄)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (inv_mem ha)
        · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := ha
          refine Or.inr ⟨b₂⁻¹ * (n i ^ 2)⁻¹, mul_mem (inv_mem hb₂) hsq, b₁⁻¹, inv_mem hb₁, ?_⟩
          rw [nrep_simple]
          group }
  have hn : n i ∈ S := Or.inr ⟨1, one_mem _, 1, one_mem _, by rw [nrep_simple]; group⟩
  have hBS : borel D H ≤ S := fun b hb => Or.inl hb
  have hLS : rankOne D.rootGroup i ≤ S := by
    refine sup_le (fun x hx => Or.inl (rootGroup_le_borel
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) (ht_single_pos i) hx))
      fun x hx => ?_
    have hy := (actsAs_n hct i).inv_conj_mem (steinbergAut_neg_single_mem_roots i) hx
    rw [((coxeterMatrix D.isFiniteType).toCoxeterSystem).inv_simple, map_neg,
      weylAction_simple_single, neg_neg] at hy
    have hyS : (n i)⁻¹ * x * n i ∈ S := hBS (rootGroup_le_borel
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) (ht_single_pos i) hy)
    have e : x = n i * ((n i)⁻¹ * x * n i) * (n i)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hn hyS) (inv_mem hn)
  exact sup_le hBS hLS hg

theorem minParabolic_inf_negUnipotent {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) [Finite K] (i : Fin D.rank) :
    (borel D H ⊔ rankOne D.rootGroup i) ⊓ negUnipotent D = D.rootGroup (-Pi.single i 1) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgP, hgU⟩ := Subgroup.mem_inf.1 hg
    have hgU' : g ∈ (negUnipotent D : Set K) := hgU
    rw [SetLike.mem_coe, negUnipotent_eq_sup hext i, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ (rootGroup_neg_single_le_normalizer hext i),
      Set.mem_mul] at hgU'
    obtain ⟨y, hy, v, hv, rfl⟩ := hgU'
    have hvP : v ∈ borel D H ⊔ rankOne D.rootGroup i :=
      Subgroup.mem_sup_right (Subgroup.mem_sup_right hv)
    have hyP : y ∈ borel D H ⊔ rankOne D.rootGroup i := by
      have := mul_mem hgP (inv_mem hvP)
      simpa using this
    rcases mem_borel_or_mem_bruhatCell_of_mem_minParabolic hct hext i hyP with hyB | hyC
    · have : y ∈ borel D H ⊓ negUnipotent D := ⟨hyB, negUnipotentExcept_le_negUnipotent i hy⟩
      rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at this
      rw [this, one_mul]
      exact hv
    · exfalso
      obtain ⟨b, hb, u, hu, e⟩ := exists_eq_mul_nrep_mul hct hext hyC
      rw [nrep_simple] at e
      have hu' := steinbergAut_inversionUnipotent_simple_le hext i hu
      have h1 : n i * u * (n i)⁻¹ ∈ negUnipotent D := by
        have := (actsAs_n hct i).conj_mem
          ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) hu'
        rw [weylAction_simple_single] at this
        exact rootGroup_le_negUnipotent (steinbergAut_neg_single_mem_roots i)
          (ht_neg_single_neg i) this
      have h2 : n i * y⁻¹ * (n i)⁻¹ ∈ negUnipotent D :=
        negUnipotentExcept_le_negUnipotent i (conj_n_mem_negUnipotentExcept hct i (inv_mem hy))
      have h3 : b⁻¹ * (n i ^ 2)⁻¹ * n i ∈ negUnipotent D := by
        have e' : b⁻¹ * (n i ^ 2)⁻¹ * n i = n i * u * (n i)⁻¹ * (n i * y⁻¹ * (n i)⁻¹) := by
          rw [e]
          group
        rw [e']
        exact mul_mem h1 h2
      exact notMem_negUnipotent_mul_n hct hext i
        (mul_mem (inv_mem hb) (inv_mem (iSup_le_borel (sq_n_mem_iSup hct i)))) h3
  · exact le_inf (le_sup_of_le_right le_sup_right)
      (rootGroup_le_negUnipotent (steinbergAut_neg_single_mem_roots i) (ht_neg_single_neg i))

theorem n_notMem_borel {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank) : n i ∉ borel D H := fun h =>
  n_notMem_normalizer hct hext i (posUnipotent_inf_negUnipotent hext)
    (rootGroup_le_posUnipotent ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
      (ht_single_pos i)) (borel_le_normalizer_posUnipotent hct h)

theorem n_mem_bruhatCell {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (i : Fin D.rank) :
    n i ∈ bruhatCell hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) :=
  ⟨1, one_mem _, 1, one_mem _, by rw [nrep_simple]; group⟩

theorem minParabolic_le {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {P : Subgroup K} (hP : borel D H ≤ P) {i : Fin D.rank} (hn : n i ∈ P) :
    borel D H ⊔ rankOne D.rootGroup i ≤ P := by
  have hα := (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  refine sup_le hP (sup_le ((rootGroup_le_borel hα (ht_single_pos i)).trans hP) fun x hx => ?_)
  have hy := (actsAs_n hct i).inv_conj_mem (steinbergAut_neg_single_mem_roots i) hx
  rw [((coxeterMatrix D.isFiniteType).toCoxeterSystem).inv_simple, map_neg,
    weylAction_simple_single, neg_neg] at hy
  have e : x = n i * ((n i)⁻¹ * x * n i) * (n i)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hn (hP (rootGroup_le_borel hα (ht_single_pos i) hy))) (inv_mem hn)

theorem eq_of_n_mem_minParabolic {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (h : n j ∈ borel D H ⊔ rankOne D.rootGroup i) : j = i := by
  rcases mem_borel_or_mem_bruhatCell_of_mem_minParabolic hct hext i h with h' | h'
  · exact absurd h' (n_notMem_borel hct hext j)
  · exact ((coxeterMatrix D.isFiniteType).toCoxeterSystem).simple_injective
      (eq_of_mem_bruhatCell hct hext (n_mem_bruhatCell hct j) h')

theorem minParabolic_atoms {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) :
    (∀ i, borel D H < borel D H ⊔ rankOne D.rootGroup i) ∧
    (∀ i, ∀ P : Subgroup K, borel D H ≤ P → P ≤ borel D H ⊔ rankOne D.rootGroup i →
      P = borel D H ∨ P = borel D H ⊔ rankOne D.rootGroup i) ∧
    (∀ P : Subgroup K, borel D H < P → ∃ i, borel D H ⊔ rankOne D.rootGroup i ≤ P) ∧
    Function.Injective fun i => borel D H ⊔ rankOne D.rootGroup i := by
  have hnP : ∀ i, n i ∈ borel D H ⊔ rankOne D.rootGroup i := fun i =>
    Subgroup.mem_sup_right (hct.n_mem i)
  have hex : ∀ P : Subgroup K, borel D H < P → ∃ i, n i ∈ P := by
    intro P hP
    by_contra hc
    push Not at hc
    exact hP.2 (le_borel_of_forall_n_notMem hct hext hP.1 hc)
  refine ⟨fun i => lt_of_le_of_ne le_sup_left fun h => n_notMem_borel hct hext i (h ▸ hnP i),
    fun i P hBP hPP => ?_, fun P hP => ?_, fun i j hij => ?_⟩
  · by_cases hPB : P = borel D H
    · exact Or.inl hPB
    · obtain ⟨j, hj⟩ := hex P (lt_of_le_of_ne hBP (Ne.symm hPB))
      obtain rfl := eq_of_n_mem_minParabolic hct hext (hPP hj)
      exact Or.inr (le_antisymm hPP (minParabolic_le hct hBP hj))
  · obtain ⟨i, hi⟩ := hex P hP
    exact ⟨i, minParabolic_le hct hP.1 hi⟩
  · have h : n j ∈ borel D H ⊔ rankOne D.rootGroup i := by
      have := hnP j
      simp only at hij
      rwa [← hij] at this
    exact (eq_of_n_mem_minParabolic hct hext h).symm

theorem exists_eq_single_of_nonneg_of_sum_eq_one {r : ℕ} {γ : Fin r → ℤ} (h0 : 0 ≤ γ)
    (h1 : ∑ j, γ j = 1) : ∃ k, γ = Pi.single k 1 := by
  obtain ⟨k, hk⟩ : ∃ k, γ k ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [Finset.sum_eq_zero fun j _ => hc j] at h1
    exact zero_ne_one h1
  refine ⟨k, funext fun j => ?_⟩
  have hsplit : γ k + ∑ x ∈ Finset.univ.erase k, γ x = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    exact h1
  have hrest : 0 ≤ ∑ x ∈ Finset.univ.erase k, γ x := Finset.sum_nonneg fun x _ => h0 x
  have hk0 : 0 ≤ γ k := h0 k
  by_cases hjk : j = k
  · subst hjk
    simp only [Pi.single_eq_same]
    omega
  · have hj := Finset.single_le_sum (fun x _ => h0 x)
      (Finset.mem_erase.2 ⟨hjk, Finset.mem_univ j⟩)
    have hj0 : 0 ≤ γ j := h0 j
    simp only [Pi.single_apply, hjk, if_false]
    omega

theorem ht_sum_smul {r : ℕ} (c : Fin r → ℤ) (v : Fin r → Fin r → ℤ) :
    ht (∑ k, c k • v k) = ∑ k, c k * ht (v k) := by
  simp only [ht, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem exists_perm_weylAction_w₀ {K : Type*} [Group K] {D : UniversalRootDatum K}
    {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hmax : ∀ w, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).length w ≤
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem).length w₀) :
    ∃ σ : Equiv.Perm (Fin D.rank), ∀ i,
      weylAction D.isFiniteType w₀ (Pi.single i 1) = -Pi.single (σ i) 1 := by
  have hw₀ := forall_isRightDescent_of_length_le hmax
  have hw₀' : ∀ i, ((coxeterMatrix D.isFiniteType).toCoxeterSystem).IsRightDescent w₀⁻¹ i :=
    forall_isRightDescent_of_length_le fun w => by
      rw [((coxeterMatrix D.isFiniteType).toCoxeterSystem).length_inv]; exact hmax w
  have hsm := (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem
  have key : ∀ j, ∃ k, weylAction D.isFiniteType w₀ (Pi.single j 1) = -Pi.single k 1 := by
    intro j
    obtain ⟨β, hβ⟩ : ∃ β, β = -weylAction D.isFiniteType w₀ (Pi.single j 1) := ⟨_, rfl⟩
    have hβ0 : 0 ≤ β := hβ ▸ neg_nonneg.2 ((isRightDescent_iff _ w₀ j).1 (hw₀ j))
    have hβht : 0 < ∑ k, β k := by
      have := ht_weylAction_neg hw₀ (hsm j) (ht_single_pos j)
      have e : ht β = -ht (weylAction D.isFiniteType w₀ (Pi.single j 1)) := by rw [hβ, ht_neg]
      change 0 < ht β
      omega
    have hback : Pi.single j 1 =
        ∑ k, β k • (-weylAction D.isFiniteType w₀⁻¹ (Pi.single k 1)) := by
      have e : -weylAction D.isFiniteType w₀⁻¹ β = Pi.single j 1 := by
        rw [hβ, map_neg, neg_neg, weylAction_inv_apply_apply]
      rw [← e]
      conv_lhs => rw [← sum_smul_single β]
      simp only [map_sum, map_zsmul, smul_neg, Finset.sum_neg_distrib]
    have hh : ∀ k, 1 ≤ ht (-weylAction D.isFiniteType w₀⁻¹ (Pi.single k 1)) := fun k => by
      have := ht_weylAction_neg hw₀' (hsm k) (ht_single_pos k)
      rw [ht_neg]
      omega
    have h1 : ∑ k, β k * ht (-weylAction D.isFiniteType w₀⁻¹ (Pi.single k 1)) = 1 := by
      rw [← ht_sum_smul, ← hback, ht_single]
    have h2 : ∑ k, β k ≤ 1 := h1 ▸ Finset.sum_le_sum fun k _ =>
      le_mul_of_one_le_right (hβ0 k) (hh k)
    obtain ⟨k, hk⟩ := exists_eq_single_of_nonneg_of_sum_eq_one hβ0 (by omega)
    exact ⟨k, by rw [← hk, hβ, neg_neg]⟩
  choose σ hσ using key
  have hinj : Function.Injective σ := by
    intro i j hij
    have e : (Pi.single i 1 : Fin D.rank → ℤ) = Pi.single j 1 := by
      have := congrArg (weylAction D.isFiniteType w₀⁻¹) ((hσ i).trans (hij ▸ (hσ j).symm))
      rwa [weylAction_inv_apply_apply, weylAction_inv_apply_apply] at this
    by_contra hne
    have := congrFun e i
    simp [Pi.single_apply, hne] at this
  exact ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj), hσ⟩

theorem rootGroup_single_le_centralizer {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hext : SteinbergExtras D n H) {i k : Fin D.rank} (hik : i ≠ k) :
    D.rootGroup (Pi.single i 1) ≤ Subgroup.centralizer (D.rootGroup (-Pi.single k 1) : Set K) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hlin : LinIndepPair (Pi.single i 1 : Fin D.rank → ℤ) (-Pi.single k 1) := by
    intro a b hab
    have hi := congrFun hab i
    have hk := congrFun hab k
    simp [Pi.single_apply, hik, Ne.symm hik] at hi hk
    exact ⟨hi, hk⟩
  have hempty : openCone D.roots (Pi.single i 1) (-Pi.single k 1) = ∅ := by
    ext γ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hγ, a, b, ha, hb, rfl⟩
    rcases nonneg_or_nonpos D.isFiniteType D.divisible hγ with h | h
    · have := h k
      simp [Pi.single_apply, Ne.symm hik] at this
      omega
    · have := h i
      simp [Pi.single_apply, hik] at this
      omega
  have hc := hext.commutator_mem _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
    _ (steinbergAut_neg_single_mem_roots k) hlin x hx y hy
  rw [hempty] at hc
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at hc
  rw [commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc.symm

theorem steinbergAut_not_map_le_centralizer {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hext : SteinbergExtras D n H) [Finite K] {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) (hodd : Nat.Coprime 2 (Nat.card ψ.ker))
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ)) (i : Fin D.rank) :
    ¬ (D.rootGroup (Pi.single i 1)).map ψ ≤
      Subgroup.centralizer (((D.rootGroup (-Pi.single i 1)).map ψ : Subgroup G) : Set G) := by
  intro hc
  have hsi := (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hXn := hX _ (steinbergAut_neg_single_mem_roots (D := D) i)
  have key : ∀ x ∈ D.rootGroup (Pi.single i 1), ∀ y ∈ D.rootGroup (-Pi.single i 1),
      x * y * x⁻¹ ∈ D.rootGroup (-Pi.single i 1) := by
    intro x hx y hy
    have hle : (D.rootGroup (-Pi.single i 1)).map (MulAut.conj x).toMonoidHom ≤
        D.rootGroup (-Pi.single i 1) := by
      refine steinbergAut_le_of_map_le ψ hker hodd hXn (hXn.map _) ?_
      rintro _ ⟨_, ⟨y', hy', rfl⟩, rfl⟩
      refine ⟨y', hy', ?_⟩
      have hcomm := Subgroup.mem_centralizer_iff.1 (hc ⟨x, hx, rfl⟩) (ψ y') ⟨y', hy', rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      rw [← hcomm, mul_inv_cancel_right]
    exact hle ⟨y, hy, rfl⟩
  apply hext.ne_bot _ hsi
  rw [eq_bot_iff]
  intro x hx
  have hn : x ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) := by
    refine Subgroup.mem_normalizer_iff.2 fun y => ⟨key x hx y, fun h => ?_⟩
    have := key x⁻¹ (inv_mem hx) _ h
    simpa [mul_assoc] using this
  rw [Subgroup.mem_bot]
  exact hext.eq_one_of_mem_normalizer i x hx hn

theorem inv_n_mul_mem_H {K : Type*} [Group K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) [Finite K] (j : Fin D.rank) {y : K}
    (hy : y ∈ rankOne D.rootGroup j)
    (h₁ : (D.rootGroup (Pi.single j 1)).map (MulAut.conj y).toMonoidHom =
      D.rootGroup (-Pi.single j 1))
    (h₂ : (D.rootGroup (-Pi.single j 1)).map (MulAut.conj y).toMonoidHom =
      D.rootGroup (Pi.single j 1)) :
    (n j)⁻¹ * y ∈ H j := by
  have hmemN : ∀ (S : Subgroup K) (g : K), S.map (MulAut.conj g).toMonoidHom = S →
      g ∈ Subgroup.normalizer (S : Set K) := by
    intro S g hS
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hS]; exact ⟨x, hx, rfl⟩
    · rw [← hS] at hx
      obtain ⟨s, hs, e⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
      have : s = x := by simpa using e
      rwa [← this]
  have hsj := (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  have hninv := (actsAs_n hct j).inv
  have hss : (((coxeterMatrix D.isFiniteType).toCoxeterSystem).simple j)⁻¹ =
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem).simple j :=
    ((coxeterMatrix D.isFiniteType).toCoxeterSystem).inv_simple j
  have hmap : ∀ (S : Subgroup K) (a b : K),
      S.map (MulAut.conj (a * b)).toMonoidHom =
        (S.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro S a b
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  refine mem_H_of_mem_rankOne hct hext j (mul_mem (inv_mem (hct.n_mem j)) hy) ?_ ?_
  · refine hmemN _ _ ?_
    rw [hmap, h₁, hninv _ (steinbergAut_neg_single_mem_roots j), hss, map_neg,
      weylAction_simple_single,
      neg_neg]
  · refine hmemN _ _ ?_
    rw [hmap, h₂, hninv _ hsj, hss, weylAction_simple_single]

end CFSG.StandardType.SteinbergAut
