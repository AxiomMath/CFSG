module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRow
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (AutNoE27 conj_injective_of_center_eq_bot
  mem_inner_of_pow_three)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.GH74.GLS (pPrimeCoreOf)

section Inner

variable {S : Type} [Group S] [Finite S]

theorem rowS148_of_inner (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      ∀ R : Subgroup S,
        (∀ e ∈ E, e ≠ 1 → R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set S))) → R = ⊥) :
    RowS148 S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro F E X R hc
  set ι : S →* MulAut S := MulAut.conj with hι
  have hinj : Function.Injective ι := conj_injective_of_center_eq_bot hZ
  have hFι : F ≤ ι.range := fun f hf => mem_inner_of_pow_three hout (hc.isE27.1.2 f hf)
  have hEι : E ≤ ι.range := hc.le.trans hFι
  set E' := E.comap ι with hE'
  have hE'map : E'.map ι = E := Subgroup.map_comap_eq_self hEι
  have hE'card : Nat.card E' = 9 := by
    rw [← hc.card, ← hE'map, Subgroup.card_map_of_injective hinj]
  have hE'ab : CFSG.Assembly.IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val ((hc.isE27.1.1).is_comm.comm ⟨ι x, hc.le x.2⟩ ⟨ι y, hc.le y.2⟩)
    · rw [map_pow, map_one]
      exact hc.isE27.1.2 _ (hc.le hx)
  set R₀ := (R ⊓ ι.range).comap ι with hR₀
  have hR₀bot : R₀ = ⊥ := by
    refine h E' hE'ab hE'card R₀ fun e' he' he'1 => ?_
    have he : ι e' ∈ E := he'
    have he1 : ι e' ≠ 1 := fun h1 => he'1 (hinj (by rw [h1, map_one]))
    set W := (pPrimeCoreOf 3 (X ⊓ Subgroup.centralizer ({ι e'} : Set (MulAut S))) ⊓
      ι.range).comap ι with hW
    have hR₀W : R₀ ≤ W := fun s hs => ⟨hc.le_core _ he he1 hs.1, hs.2⟩
    refine hR₀W.trans (Sec14.le_pPrimeCoreOf ?_ ?_ ?_)
    ·
      intro s hs
      have h1 : ι s ∈ Subgroup.centralizer ({ι e'} : Set (MulAut S)) :=
        (Subgroup.mem_inf.mp (Sec14.pPrimeCoreOf_le 3 _ hs.1)).2
      rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
      apply hinj
      rw [map_mul, map_mul]
      exact h1
    ·
      intro c hc'
      have hcC : ι c ∈ Subgroup.centralizer ({ι e'} : Set (MulAut S)) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc' ⊢
        rw [← map_mul, ← map_mul, hc']
      have hcX : ι c ∈ X ⊓ Subgroup.centralizer ({ι e'} : Set (MulAut S)) :=
        Subgroup.mem_inf.mpr ⟨hc.inner_le ⟨c, rfl⟩, hcC⟩
      have hn1 := Sec14.le_normalizer_pPrimeCoreOf 3 _ hcX
      rw [Subgroup.mem_normalizer_iff] at hn1 ⊢
      intro s
      simp only [hW, Subgroup.mem_comap, Subgroup.mem_inf, map_mul, map_inv]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(hn1 _).mp h1, Subgroup.mul_mem _ (Subgroup.mul_mem _ ⟨c, rfl⟩ h2)
          (Subgroup.inv_mem _ ⟨c, rfl⟩)⟩
      · rintro ⟨h1, -⟩
        exact ⟨(hn1 _).mpr h1, ⟨s, rfl⟩⟩
    ·
      have hle : W.map ι ≤ pPrimeCoreOf 3 (X ⊓ Subgroup.centralizer ({ι e'} : Set (MulAut S))) := by
        rintro _ ⟨s, hs, rfl⟩
        exact hs.1
      rw [← Subgroup.card_map_of_injective hinj]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
        (Sec14.coprime_card_pPrimeCoreOf 3 _)
  have hRι : R ⊓ ι.range = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨s, rfl⟩ := hx.2
    have hs : s ∈ R₀ := hx
    rw [hR₀bot, Subgroup.mem_bot] at hs
    rw [hs, map_one]
    exact Subgroup.one_mem _
  rw [hc.eq_commutator, eq_bot_iff, ← hRι]
  rw [Subgroup.commutator_le]
  intro r hr f hf
  refine ⟨?_, ?_⟩
  · have : r * f * r⁻¹ * f⁻¹ = r * (f * r⁻¹ * f⁻¹) := by group
    rw [commutatorElement_def, this]
    exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hc.le_normalizer hf) _).mp (R.inv_mem hr))
  · haveI : ι.range.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S
    rw [commutatorElement_def]
    exact ι.range.mul_mem (this.conj_mem _ (hFι hf) r) (ι.range.inv_mem (hFι hf))

theorem comap_inf_inner_le_pPrimeCoreOf (hZ : Subgroup.center S = ⊥) {X R : Subgroup (MulAut S)}
    (hX : (MulAut.conj : S →* MulAut S).range ≤ X) {s : S}
    (hR : R ≤ pPrimeCoreOf 3 (X ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S)))) :
    (R ⊓ (MulAut.conj : S →* MulAut S).range).comap MulAut.conj ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set S)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ι : S →* MulAut S := MulAut.conj with hι
  have hinj : Function.Injective ι := conj_injective_of_center_eq_bot hZ
  set W := (pPrimeCoreOf 3 (X ⊓ Subgroup.centralizer ({ι s} : Set (MulAut S))) ⊓
    ι.range).comap ι with hW
  have hRW : (R ⊓ ι.range).comap ι ≤ W := fun t ht => ⟨hR ht.1, ht.2⟩
  refine hRW.trans (Sec14.le_pPrimeCoreOf ?_ ?_ ?_)
  · intro t ht
    have h1 : ι t ∈ Subgroup.centralizer ({ι s} : Set (MulAut S)) :=
      (Subgroup.mem_inf.mp (Sec14.pPrimeCoreOf_le 3 _ ht.1)).2
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    apply hinj
    rw [map_mul, map_mul]
    exact h1
  · intro c hc'
    have hcC : ι c ∈ Subgroup.centralizer ({ι s} : Set (MulAut S)) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc' ⊢
      rw [← map_mul, ← map_mul, hc']
    have hcX : ι c ∈ X ⊓ Subgroup.centralizer ({ι s} : Set (MulAut S)) :=
      Subgroup.mem_inf.mpr ⟨hX ⟨c, rfl⟩, hcC⟩
    have hn1 := Sec14.le_normalizer_pPrimeCoreOf 3 _ hcX
    rw [Subgroup.mem_normalizer_iff] at hn1 ⊢
    intro t
    simp only [hW, Subgroup.mem_comap, Subgroup.mem_inf, map_mul, map_inv]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hn1 _).mp h1, Subgroup.mul_mem _ (Subgroup.mul_mem _ ⟨c, rfl⟩ h2)
        (Subgroup.inv_mem _ ⟨c, rfl⟩)⟩
    · rintro ⟨h1, -⟩
      exact ⟨(hn1 _).mpr h1, ⟨t, rfl⟩⟩
  · have hle : W.map ι ≤ pPrimeCoreOf 3 (X ⊓ Subgroup.centralizer ({ι s} : Set (MulAut S))) := by
      rintro _ ⟨t, ht, rfl⟩
      exact ht.1
    rw [← Subgroup.card_map_of_injective hinj]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      (Sec14.coprime_card_pPrimeCoreOf 3 _)

theorem rowS148_of_inndiag (hZ : Subgroup.center S = ⊥) (D : Subgroup (MulAut S))
    (h1 : ∀ σ τ : MulAut S, σ * τ * σ⁻¹ * τ⁻¹ ∈ D)
    (h2 : ∀ E : Subgroup (MulAut S), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      ∃ e ∈ E, e ≠ 1 ∧ e ∈ (MulAut.conj : S →* MulAut S).range)
    (h3 : ∀ s : S, orderOf s = 3 → pPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set S)) = ⊥)
    (h4 : ∀ d ∈ D, ∀ f : MulAut S, f ^ 3 = 1 →
      d * f * d⁻¹ * f⁻¹ ∈ (MulAut.conj : S →* MulAut S).range) :
    RowS148 S := by
  intro F E X R hc
  set ι : S →* MulAut S := MulAut.conj with hι
  have hinj : Function.Injective ι := conj_injective_of_center_eq_bot hZ
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := fun e he => hc.isE27.1.2 e (hc.le he)
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, hE3⟩
    apply Subtype.ext
    have := congrArg Subtype.val ((hc.isE27.1.1).is_comm.comm ⟨x, hc.le x.2⟩ ⟨y, hc.le y.2⟩)
    change (x : MulAut S) * y = y * x
    exact this
  obtain ⟨_, he₁E, he₁1, ⟨s, rfl⟩⟩ := h2 E hEab hc.card
  have hs3 : orderOf s = 3 := by
    refine orderOf_eq_prime (hinj (by rw [map_pow, hE3 _ he₁E, map_one])) ?_
    intro h
    exact he₁1 (by rw [h, map_one])
  have hRι : R ⊓ ι.range = ⊥ := by
    have hle := comap_inf_inner_le_pPrimeCoreOf hZ hc.inner_le (hc.le_core _ he₁E he₁1)
    rw [h3 s hs3, le_bot_iff] at hle
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨t, rfl⟩ := hx.2
    have ht : t ∈ (R ⊓ ι.range).comap ι := hx
    rw [hle, Subgroup.mem_bot] at ht
    rw [ht, map_one]
    exact Subgroup.one_mem _
  have hcomm_mem : ∀ r ∈ R, ∀ f ∈ F, r * f * r⁻¹ * f⁻¹ ∈ R := by
    intro r hr f hf
    have : r * f * r⁻¹ * f⁻¹ = r * (f * r⁻¹ * f⁻¹) := by group
    rw [this]
    exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hc.le_normalizer hf) _).mp (R.inv_mem hr))
  have hRD : R ≤ D := by
    rw [hc.eq_commutator, Subgroup.commutator_le]
    intro r hr f hf
    rw [commutatorElement_def]
    exact h1 r f
  rw [hc.eq_commutator, eq_bot_iff, ← hRι, Subgroup.commutator_le]
  intro r hr f hf
  rw [commutatorElement_def]
  exact ⟨hcomm_mem r hr f hf, h4 r (hRD hr) f (hc.isE27.1.2 f hf)⟩

theorem rowS148_of_pPrimeCore_eq_bot (hZ : Subgroup.center S = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ s : S, orderOf s = 3 → pPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set S)) = ⊥) :
    RowS148 S := by
  refine rowS148_of_inner hZ hout fun E hE hE9 R hR => ?_
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hE1 : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    rw [hE1, Subgroup.card_bot] at hE9
    omega
  have he3 : orderOf e = 3 :=
    orderOf_eq_prime (hE.2 e heE) he1
  exact le_bot_iff.mp (h e he3 ▸ hR e heE he1)

end Inner

section Model

variable {S G' : Type} [Group S] [Finite S] [Group G']

theorem map_pPrimeCoreOf_of_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (K : Subgroup X) :
    (pPrimeCoreOf 3 K).map f = pPrimeCoreOf 3 (K.map f) := by
  unfold pPrimeCoreOf
  let ψ : K ≃* K.map f := K.equivMapOfInjective f hf
  rw [← CFSG.pPrimeCore_map_iso 3 ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem rowS148_of_subgroupModel {P : Subgroup G'} (e : S ≃* P) (hZ : Subgroup.center S = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ x ∈ P, orderOf x = 3 →
      pPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G') ⊓ P) = ⊥) :
    RowS148 S := by
  refine rowS148_of_pPrimeCore_eq_bot hZ hout fun s hs => ?_
  set f : S →* G' := P.subtype.comp e.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hr : f.range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [f]⟩
  have hmap := RonanK429H.map_centralizer_singleton f hf s
  rw [hr] at hmap
  have hfs : orderOf (f s) = 3 := by rw [orderOf_injective f hf s]; exact hs
  have h0 := h (f s) (by rw [← hr]; exact ⟨s, rfl⟩) hfs
  rw [← hmap, ← map_pPrimeCoreOf_of_injective f hf] at h0
  exact (Subgroup.map_eq_bot_iff_of_injective _ hf).mp h0

end Model

section Criteria

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_eq_bot_of_selfCentralizing {C P : Subgroup G} (hPC : P ≤ C)
    (hPn : ∀ g ∈ C, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hP3 : IsPGroup 3 P)
    (hcent : Subgroup.centralizer (P : Set G) ⊓ C ≤ P) : pPrimeCoreOf 3 C = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := pPrimeCoreOf 3 C with hN
  have hNC : N ≤ C := Sec14.pPrimeCoreOf_le 3 C
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := Sec14.le_normalizer_pPrimeCoreOf 3 C
  have hdisj : N ⊓ P = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := hP3.exists_card_eq
    rw [hk]
    exact (Nat.Coprime.pow_left _ (Sec14.coprime_card_pPrimeCoreOf 3 C)).symm
  rw [eq_bot_iff]
  intro n hn
  have hnP : n ∈ P := by
    refine hcent (Subgroup.mem_inf.mpr ⟨?_, hNC hn⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h1 : n * p * n⁻¹ * p⁻¹ ∈ N ⊓ P := by
      refine ⟨?_, P.mul_mem (hPn n (hNC hn) p hp) (P.inv_mem hp)⟩
      have : n * p * n⁻¹ * p⁻¹ = n * (p * n⁻¹ * p⁻¹) := by group
      rw [this]
      exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.mp (hCN (hPC hp)) _).mp (N.inv_mem hn))
    rw [hdisj, Subgroup.mem_bot] at h1
    calc p * n = (n * p * n⁻¹ * p⁻¹)⁻¹ * (n * p) := by group
      _ = n * p := by rw [h1, inv_one, one_mul]
  have : n ∈ N ⊓ P := ⟨hn, hnP⟩
  rwa [hdisj] at this

theorem pPrimeCoreOf_eq_bot_of_simpleNormal {C L : Subgroup G} (hLC : L ≤ C)
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) [hLs : IsSimpleGroup L] (hL3 : 3 ∣ Nat.card L)
    (hcent : ∀ g ∈ C, (∀ l ∈ L, l * g = g * l) → g ^ 3 = 1) : pPrimeCoreOf 3 C = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := pPrimeCoreOf 3 C with hN
  have hNC : N ≤ C := Sec14.pPrimeCoreOf_le 3 C
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := Sec14.le_normalizer_pPrimeCoreOf 3 C
  have hNcop : Nat.Coprime 3 (Nat.card N) := Sec14.coprime_card_pPrimeCoreOf 3 C
  have hNL : N ⊓ L = ⊥ := by
    have hnormal : ((N ⊓ L).subgroupOf L).Normal := by
      refine ⟨fun x hx l => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hCN (hLC l.2)) _).mp hx.1,
        L.mul_mem (L.mul_mem l.2 hx.2) (L.inv_mem l.2)⟩
    haveI := hnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ L).subgroupOf L) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : L) ∈ (N ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    · exfalso
      have hLN : L ≤ N := fun l hl => by
        have : (⟨l, hl⟩ : L) ∈ (N ⊓ L).subgroupOf L := by rw [h]; trivial
        exact (Subgroup.mem_subgroupOf.mp this).1
      have := Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLN) hNcop
      exact absurd (Nat.Coprime.eq_one_of_dvd this hL3) (by norm_num)
  rw [eq_bot_iff]
  intro n hn
  have hn3 : n ^ 3 = 1 := by
    refine hcent n (hNC hn) fun l hl => ?_
    have h1 : n * l * n⁻¹ * l⁻¹ ∈ N ⊓ L := by
      refine ⟨?_, L.mul_mem (hLn n (hNC hn) l hl) (L.inv_mem hl)⟩
      have : n * l * n⁻¹ * l⁻¹ = n * (l * n⁻¹ * l⁻¹) := by group
      rw [this]
      exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.mp (hCN (hLC hl)) _).mp (N.inv_mem hn))
    rw [hNL, Subgroup.mem_bot] at h1
    calc l * n = (n * l * n⁻¹ * l⁻¹)⁻¹ * (n * l) := by group
      _ = n * l := by rw [h1, inv_one, one_mul]
  have hord : orderOf n ∣ Nat.gcd 3 (Nat.card N) := by
    refine Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn3) ?_
    have := Subgroup.orderOf_dvd_natCard N hn
    exact this
  rw [hNcop, Nat.dvd_one, orderOf_eq_one_iff] at hord
  rw [Subgroup.mem_bot]
  exact hord

theorem pPrimeCoreOf_eq_bot_of_isQuasisimple {C : Subgroup G} (hq : IsQuasisimple C)
    (hZ : IsPGroup 3 (Subgroup.center C)) (h3 : 3 ∣ Nat.card C) : pPrimeCoreOf 3 C = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [pPrimeCoreOf, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective]
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (CFSG.pPrimeCore_normal (p := 3) (G := C)) with h | h
  · exfalso
    have hcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 C)) := CFSG.pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hcop
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
  · have hdisj : CFSG.pPrimeCore 3 C ⊓ Subgroup.center C = ⊥ := by
      refine Subgroup.inf_eq_bot_of_coprime ?_
      obtain ⟨k, hk⟩ := hZ.exists_card_eq
      rw [hk]
      exact (Nat.Coprime.pow_left _ CFSG.pPrimeCore_coprime_card).symm
    rwa [inf_eq_left.mpr h] at hdisj

theorem pPrimeCoreOf_eq_bot_of_isPGroup {C : Subgroup G} (hC : IsPGroup 3 C) :
    pPrimeCoreOf 3 C = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Sec14.pPrimeCoreOf_le 3 C
  have hp : IsPGroup 3 (pPrimeCoreOf 3 C) := hC.to_le hle
  have hcop := Sec14.coprime_card_pPrimeCoreOf 3 C
  rcases hp.card_eq_or_dvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)

theorem pPrimeCoreOf_centralizer_conj {P : Subgroup G} {y k : G} (hk : k ∈ P) (hy : y ^ 3 = 1)
    {e : ℕ} (he : e = 1 ∨ e = 2)
    (h : pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G) ⊓ P) = ⊥) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set G) ⊓ P) = ⊥ := by
  have hmap : (Subgroup.centralizer ({y} : Set G) ⊓ P).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set G) ⊓ P := by
    rw [← RonanK429H.centralizer_pow_of_pow_three hy he]
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
      refine ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩
      calc k * z * k⁻¹ * (k * y ^ e * k⁻¹) = k * (z * y ^ e) * k⁻¹ := by group
        _ = k * (y ^ e * z) * k⁻¹ := by rw [hzc]
        _ = k * y ^ e * k⁻¹ * (k * z * k⁻¹) := by group
    · rintro ⟨hwc, hwP⟩
      refine ⟨k⁻¹ * w * k, ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hwP) hk⟩, by group⟩
      calc k⁻¹ * w * k * y ^ e = k⁻¹ * (w * (k * y ^ e * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * y ^ e * k⁻¹) * w) * k := by rw [hwc]
        _ = y ^ e * (k⁻¹ * w * k) := by group
  rw [← hmap, ← Sec14.map_pPrimeCoreOf, h, Subgroup.map_bot]

theorem pPrimeCoreOf_centralizer_of_isConj {y z : G} (hyz : IsConj y z)
    (h : pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G)) = ⊥) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hyz
  have hmap : (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * y * c⁻¹} : Set G) := by
    rw [map_centralizer_singleton]
    rfl
  rw [← hmap, ← Sec14.map_pPrimeCoreOf, h, Subgroup.map_bot]

theorem pPrimeCoreOf_centralizer_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : ∀ t : T, orderOf t = 3 → pPrimeCoreOf 3 (Subgroup.centralizer ({t} : Set T)) = ⊥) :
    ∀ s : S, orderOf s = 3 → pPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set S)) = ⊥ := by
  intro s hs
  have h1 := h (e s) (by rw [MulEquiv.orderOf_eq]; exact hs)
  rw [← map_centralizer_singleton, ← Sec14.map_pPrimeCoreOf] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

end Criteria

theorem rowSOf148_spor {s : TauCeti.SporadicName}
    (hb : Nonempty (Blueprint.NativeSporadic.Carrier s ≃* Spor s))
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s) → RowS148 S) :
    RowSOf148 (Spor s) := fun S _ _ hs hna ⟨e⟩ => by
  obtain ⟨b⟩ := hb
  exact h S hs hna ⟨e.trans b.symm⟩

theorem rowSOf148_of_noE27 {T : Type} [Group T]
    (h : ¬ 3 ∣ Nat.card (Outer T) ∧ RonanK429.NoE27 T) : RowSOf148 T :=
  rowSOf148_of_autNoE27 fun _ _ _ hs hna ⟨e⟩ =>
    RonanK429.autNoE27_of_mulEquiv_of_noE27 e hs hna h.1 h.2

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
