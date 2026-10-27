module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Lift
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartTwo.Sec13.F135LastAct

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem r5d_card_comap {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (F : Subgroup H) (hF : F ≤ f.range) :
    Nat.card (F.comap f) = Nat.card f.ker * Nat.card F := by
  have h1 := Subgroup.card_mul_index (F.comap f)
  rw [Subgroup.index_comap] at h1
  have h2 := Subgroup.card_ker_mul_card_range f
  have h3 := Subgroup.relIndex_mul_card F f.range
  rw [inf_eq_left.mpr hF] at h3
  have hr : 0 < F.relIndex f.range := by
    rcases Nat.eq_zero_or_pos (F.relIndex f.range) with h | h
    · rw [h, mul_zero] at h1
      exact absurd h1.symm (Nat.card_pos (α := G)).ne'
    · exact h
  apply Nat.eq_of_mul_eq_mul_right hr
  rw [h1, ← h2, ← h3]
  ring

theorem r5d_inf_bot {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (R : Subgroup M)
    [R.Normal] (hR : ¬ p ∣ Nat.card R) (E : Subgroup M) (hE : IsPGroup p E) :
    E ⊓ R = ⊥ := by
  haveI := Fact.mk hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE
  have hdvd : Nat.card (E ⊓ R : Subgroup M) ∣ p ^ k := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : E ⊓ R ≤ E)
    rwa [hk] at h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hnd : ¬ p ∣ Nat.card (E ⊓ R : Subgroup M) := fun h =>
    hR (h.trans (Subgroup.card_dvd_of_le (inf_le_right : E ⊓ R ≤ R)))
  have hi0 : i = 0 := by
    by_contra hne
    apply hnd
    rw [hi]
    exact dvd_pow_self p hne
  exact (Subgroup.eq_bot_iff_card _).mpr (by rw [hi, hi0, pow_zero])

@[expose] noncomputable def r5d_psi {M : Type} [Group M] (R : Subgroup M) [R.Normal]
    (E : Subgroup M) (J : Subgroup (M ⧸ R))
    (hEN : E.map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (J : Set (M ⧸ R))) :
    E →* MulAut (J ⧸ Subgroup.center J) :=
  (actS J).comp (((QuotientGroup.mk' R).comp E.subtype).codRestrict
    (Subgroup.normalizer (J : Set (M ⧸ R))) fun e => hEN (Subgroup.mem_map_of_mem _ e.2))

theorem r5d_psi_eq_one_iff {M : Type} [Group M] (R : Subgroup M) [R.Normal] (E Y : Subgroup M)
    (hYE : Y ≤ E) (hYc : Y ≤ Subgroup.center M) (hEbot : E ⊓ R = ⊥)
    (J : Subgroup (M ⧸ R)) (hJ : Group.IsPerfect J)
    (hEN : E.map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (J : Set (M ⧸ R)))
    (hker : Subgroup.centralizer (J : Set (M ⧸ R)) ⊓ E.map (QuotientGroup.mk' R) ≤
      Y.map (QuotientGroup.mk' R))
    (e : E) : r5d_psi R E J hEN e = 1 ↔ (e : M) ∈ Y := by
  show actS J ⟨QuotientGroup.mk' R (e : M), hEN (Subgroup.mem_map_of_mem _ e.2)⟩ = 1 ↔
    (e : M) ∈ Y
  rw [actS_eq_one_iff hJ]
  constructor
  · intro h
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp
      (hker ⟨h, Subgroup.mem_map_of_mem _ e.2⟩)
    have hye' : (QuotientGroup.mk y : M ⧸ R) = QuotientGroup.mk (e : M) := hye
    have hmem : y⁻¹ * (e : M) ∈ E ⊓ R :=
      ⟨E.mul_mem (E.inv_mem (hYE hy)) e.2, QuotientGroup.eq.mp hye'⟩
    rw [hEbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    rw [← hmem]
    exact hy
  · intro he
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
    show QuotientGroup.mk' R g * QuotientGroup.mk' R (e : M) =
      QuotientGroup.mk' R (e : M) * QuotientGroup.mk' R g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hYc he) g]

theorem r5d_comm {M : Type} [Group M] (R : Subgroup M) [R.Normal] (E Y : Subgroup M)
    (hYE : Y ≤ E) (hYc : Y ≤ Subgroup.center M) (hEbot : E ⊓ R = ⊥)
    (hYΦ : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ Y → x * y * x⁻¹ * y⁻¹ = 1)
    (J : Subgroup (M ⧸ R)) (hJ : Group.IsPerfect J)
    (hEN : E.map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (J : Set (M ⧸ R)))
    (hker : Subgroup.centralizer (J : Set (M ⧸ R)) ⊓ E.map (QuotientGroup.mk' R) ≤
      Y.map (QuotientGroup.mk' R))
    (F : Subgroup (MulAut (J ⧸ Subgroup.center J)))
    (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (x y : E) (hx : r5d_psi R E J hEN x ∈ F) (hy : r5d_psi R E J hEN y ∈ F) :
    (x : M) * y = y * x := by
  have hψc : r5d_psi R E J hEN (x * y * x⁻¹ * y⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hFc _ hx _ hy]
    group
  have hmemY := (r5d_psi_eq_one_iff R E Y hYE hYc hEbot J hJ hEN hker _).mp hψc
  have hmem : (x : M) * y * (x : M)⁻¹ * (y : M)⁻¹ ∈ Y := hmemY
  have h1 := hYΦ (x : M) x.2 (y : M) y.2 hmem
  calc (x : M) * y = ((x : M) * y * (x : M)⁻¹ * (y : M)⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

@[expose] def r5d_K {M : Type} [Group M] (R : Subgroup M) [R.Normal] (J : Subgroup (M ⧸ R))
    (T : Subgroup (J ⧸ Subgroup.center J)) : Subgroup (M ⧸ R) :=
  (T.comap (QuotientGroup.mk' (Subgroup.center J))).map J.subtype

theorem r5d_fwd {M : Type} [Group M] (R : Subgroup M) [R.Normal] (E : Subgroup M)
    (J : Subgroup (M ⧸ R))
    (hEN : E.map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (J : Set (M ⧸ R)))
    (F : Subgroup (MulAut (J ⧸ Subgroup.center J)))
    (T : Subgroup (J ⧸ Subgroup.center J)) (hcon : ∀ φ ∈ F, T.map φ.toMonoidHom = T)
    (e : E) (he : r5d_psi R E J hEN e ∈ F) (k : M ⧸ R) (hk : k ∈ r5d_K R J T) :
    QuotientGroup.mk' R (e : M) * k * (QuotientGroup.mk' R (e : M))⁻¹ ∈ r5d_K R J T := by
  unfold r5d_K at hk ⊢
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hk
  have hjT : QuotientGroup.mk' (Subgroup.center J) j ∈ T := Subgroup.mem_comap.mp hj
  have hnj : QuotientGroup.mk' R (e : M) * (j : M ⧸ R) * (QuotientGroup.mk' R (e : M))⁻¹ ∈ J := by
    have hn : QuotientGroup.mk' R (e : M) ∈ Subgroup.normalizer (J : Set (M ⧸ R)) :=
      hEN (Subgroup.mem_map_of_mem _ e.2)
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp j.2
  refine Subgroup.mem_map.mpr ⟨(⟨_, hnj⟩ : J), ?_, rfl⟩
  have key : QuotientGroup.mk' (Subgroup.center J) (⟨_, hnj⟩ : J) =
      r5d_psi R E J hEN e (QuotientGroup.mk' (Subgroup.center J) j) := by
    exact (actS_mk J ⟨QuotientGroup.mk' R (e : M), hEN (Subgroup.mem_map_of_mem _ e.2)⟩ j).symm
  rw [Subgroup.mem_comap, key]
  have h2 := Subgroup.mem_map_of_mem (r5d_psi R E J hEN e).toMonoidHom hjT
  rw [hcon _ he] at h2
  exact h2

theorem r5d_normal {M : Type} [Group M] (R : Subgroup M) [R.Normal] (E : Subgroup M)
    (J : Subgroup (M ⧸ R))
    (hEN : E.map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (J : Set (M ⧸ R)))
    (F : Subgroup (MulAut (J ⧸ Subgroup.center J)))
    (T : Subgroup (J ⧸ Subgroup.center J)) (hcon : ∀ φ ∈ F, T.map φ.toMonoidHom = T)
    (e : E) (he : r5d_psi R E J hEN e ∈ F) :
    QuotientGroup.mk' R (e : M) ∈
      Subgroup.normalizer ((r5d_K R J T : Subgroup (M ⧸ R)) : Set (M ⧸ R)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact r5d_fwd R E J hEN F T hcon e he k hk
  · intro hk
    have he' : r5d_psi R E J hEN e⁻¹ ∈ F := by
      rw [map_inv]
      exact F.inv_mem he
    have h3 := r5d_fwd R E J hEN F T hcon e⁻¹ he' _ hk
    have e1 : ((e⁻¹ : E) : M) = (e : M)⁻¹ := rfl
    rw [e1, map_inv] at h3
    have e2 : (QuotientGroup.mk' R (e : M))⁻¹ *
        (QuotientGroup.mk' R (e : M) * k * (QuotientGroup.mk' R (e : M))⁻¹) *
        ((QuotientGroup.mk' R (e : M))⁻¹)⁻¹ = k := by
      group
    rwa [e2] at h3

theorem r5d_card_K {M : Type} [Group M] [Finite M] (R : Subgroup M) [R.Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (J : Subgroup (M ⧸ R))
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (T : Subgroup (J ⧸ Subgroup.center J))
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    ¬ p ∣ Nat.card (r5d_K R J T) ∧ 2 ∣ Nat.card (r5d_K R J T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
  have hle : T ≤ (QuotientGroup.mk' (Subgroup.center J)).range := by
    intro s _
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨j, rfl⟩
  have hcard : Nat.card (r5d_K R J T) = Nat.card (Subgroup.center J) * Nat.card T := by
    have h1 := r5d_card_comap (QuotientGroup.mk' (Subgroup.center J)) T hle
    rw [QuotientGroup.ker_mk'] at h1
    unfold r5d_K
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective J), h1]
  have hpT : ¬ p ∣ Nat.card T := by
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hT
    rw [Subgroup.eq_bot_iff_card, hn, pow_zero]
  have h2T : 2 ∣ Nat.card T := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  constructor
  · rw [hcard]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact hZ h1
    · exact hpT h1
  · rw [hcard]
    exact Dvd.dvd.mul_left h2T _

theorem r5d_sylow_props {X : Type*} [Group X] [Finite X] {K T₂ : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 T₂ K) (h2 : 2 ∣ Nat.card K) :
    T₂ ≠ ⊥ ∧ IsPGroup 2 T₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hS
  constructor
  · intro hbot
    have h1 : Nat.card (Q : Subgroup K) = 1 := by
      have h := (Subgroup.eq_bot_iff_card _).mp hbot
      rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective K)] at h
    have h3 := Subgroup.card_mul_index (Q : Subgroup K)
    rw [h1, one_mul] at h3
    apply Sylow.not_dvd_index Q
    rw [h3]
    exact h2
  · exact Q.isPGroup'.map K.subtype

theorem h2b_of_lifting {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (R : Subgroup M) [R.Normal] (hR : ¬ p ∣ Nat.card R)
    (Y E : Subgroup M) (hY : Nat.card Y = p) (hYc : Y ≤ Subgroup.center M)
    (hE : IsPGroup p E) (hEexp : ∀ e ∈ E, e ^ p = 1) (hYE : Y ≤ E)
    (hYΦ : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ Y → x * y * x⁻¹ * y⁻¹ = 1)
    (J : Subgroup (M ⧸ R)) (hJ : Group.IsPerfect J) (hZ : ¬ p ∣ Nat.card (Subgroup.center J))
    (hEN : E.map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (J : Set (M ⧸ R)))
    (hker : Subgroup.centralizer (J : Set (M ⧸ R)) ⊓ E.map (QuotientGroup.mk' R) ≤
      Y.map (QuotientGroup.mk' R))
    (hno : ∀ A T : Subgroup M, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set M)) :
    ∀ F : Subgroup (MulAut (J ⧸ Subgroup.center J)),
      F ≤ ((E.map (QuotientGroup.mk' R)).subgroupOf (Subgroup.normalizer (J : Set (M ⧸ R)))).map
        (actS J) →
      CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
      ∀ T : Subgroup (J ⧸ Subgroup.center J), T ≠ ⊥ → IsPGroup 2 T →
        ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T := by
  intro F hFP hFel hFcard T hT hT2
  by_contra hcon
  have hcon' : ∀ φ ∈ F, T.map φ.toMonoidHom = T := fun φ hφ =>
    Classical.byContradiction fun h => hcon ⟨φ, hφ, h⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEbot : E ⊓ R = ⊥ := r5d_inf_bot hp R hR E hE
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hFel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hFrange : F ≤ (r5d_psi R E J hEN).range := by
    intro φ hφ
    obtain ⟨n, hn, hnφ⟩ := Subgroup.mem_map.mp (hFP hφ)
    obtain ⟨e, he, hem⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
    refine ⟨⟨e, he⟩, ?_⟩
    have key : ∀ m : Subgroup.normalizer (J : Set (M ⧸ R)), m = n → actS J m = φ := by
      rintro m rfl
      exact hnφ
    exact key _ (Subtype.ext hem)
  have hψker : (r5d_psi R E J hEN).ker = Y.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      r5d_psi_eq_one_iff R E Y hYE hYc hEbot J hJ hEN hker e]
  have hkercard : Nat.card (r5d_psi R E J hEN).ker = p := by
    rw [hψker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYE).toEquiv, hY]
  set FE : Subgroup E := F.comap (r5d_psi R E J hEN) with hFE
  have hFEcard : Nat.card FE = p ^ 3 := by
    rw [hFE, r5d_card_comap _ F hFrange, hkercard, hFcard]
    ring
  set FM : Subgroup M := FE.map E.subtype with hFM
  have hFMcard : Nat.card FM = p ^ 3 := by
    rw [hFM, Subgroup.card_map_of_injective (Subgroup.subtype_injective E), hFEcard]
  have hFMmem : ∀ x ∈ FM, ∃ e ∈ FE, (e : M) = x := by
    intro x hx
    obtain ⟨e, he, hex⟩ := Subgroup.mem_map.mp hx
    exact ⟨e, he, hex⟩
  have hFMcomm : ∀ x ∈ FM, ∀ y ∈ FM, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hFMmem x hx
    obtain ⟨b, hb, rfl⟩ := hFMmem y hy
    exact r5d_comm R E Y hYE hYc hEbot hYΦ J hJ hEN hker F hFc a b
      (Subgroup.mem_comap.mp ha) (Subgroup.mem_comap.mp hb)
  have hFMel : CFSG.Open.IsElemAbelian p FM := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hFMcomm x.1 x.2 y.1 y.2)⟩⟩, ?_⟩
    intro x hx
    obtain ⟨e, -, rfl⟩ := hFMmem x hx
    exact hEexp _ e.2
  have hFp : IsPGroup p FM := IsPGroup.of_card (n := 3) hFMcard
  have hFMbar : IsPGroup p (FM.map (QuotientGroup.mk' R)) := hFp.map _
  have hFK : FM.map (QuotientGroup.mk' R) ≤
      Subgroup.normalizer ((r5d_K R J T : Subgroup (M ⧸ R)) : Set (M ⧸ R)) := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨e, he, rfl⟩ := hFMmem x hx
    exact r5d_normal R E J hEN F T hcon' e (Subgroup.mem_comap.mp he)
  obtain ⟨hKp, hK2⟩ := r5d_card_K R hp hp2 J hZ T hT hT2
  obtain ⟨T₂, hT₂S, hT₂N⟩ := exists_invariant_sylow_two hp hFMbar hFK hKp
  obtain ⟨hT₂ne, hT₂p⟩ := r5d_sylow_props hT₂S hK2
  obtain ⟨T', hT'ne, hT'2, hFT'⟩ := exists_two_lift hp hp2 R hR hFp hT₂ne hT₂p hT₂N
  exact hno FM T' hFMel hFMcard hT'ne hT'2 hFT'

end CFSG.RankThree.PartTwo.Sec13.F135Last
