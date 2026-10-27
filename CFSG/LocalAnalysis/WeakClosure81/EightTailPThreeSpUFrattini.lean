module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUDefs
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUFix
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveBridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

section RootData

variable {S : Type} [Group S] {ψ : ↥(kGenIn V H) →* S} {ρ : ↥H →* MulAut S}
  {R Sy : Subgroup S} {e : ℕ}

private theorem wc85fr_rho_eq_conj_psi (D : RootData V H T S ψ ρ R Sy e)
    (k : ↥(kGenIn V H)) :
    ρ ⟨(k : G), (kGenIn_le_H D.hyp.le_H) k.2⟩ = MulAut.conj (ψ k) := by
  ext s
  obtain ⟨k', rfl⟩ := D.surj s
  have hkH : (k : G) ∈ H := (kGenIn_le_H D.hyp.le_H) k.2
  have hkN : (k : G) ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) :=
    D.hyp.le_normalizer_kGenIn_of_eq_sup D.eq_sup hkH
  have hxK : (k : G) * (k' : G) * (k : G)⁻¹ ∈ kGenIn V H :=
    (Subgroup.mem_normalizer_iff.mp hkN (k' : G)).mp k'.2
  have hact := D.act ⟨(k : G), hkH⟩ k' ⟨(k : G) * (k' : G) * (k : G)⁻¹, hxK⟩ rfl
  rw [hact]
  have hmul : (⟨(k : G) * (k' : G) * (k : G)⁻¹, hxK⟩ : ↥(kGenIn V H)) =
      (⟨(k : G), k.2⟩ : ↥(kGenIn V H)) * k' * (⟨(k : G), k.2⟩ : ↥(kGenIn V H))⁻¹ :=
    Subtype.ext rfl
  rw [hmul, map_mul, map_mul, map_inv, MulAut.conj_apply]

private theorem wc85fr_map_rho_barSub (D : RootData V H T S ψ ρ R Sy e) {a : G} (ha : a ∈ H)
    {A : Subgroup G} (hA : A ≤ kGenIn V H) :
    Subgroup.map (ρ ⟨a, ha⟩).toMonoidHom (barSub (kGenIn V H) ψ A) =
      barSub (kGenIn V H) ψ (conjSubgroup A a⁻¹) := by
  classical
  have hN : a ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) :=
    D.hyp.le_normalizer_kGenIn_of_eq_sup D.eq_sup ha
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨k, hkA, rfl⟩ := mem_barSub.mp hs
    have hxK : a * (k : G) * a⁻¹ ∈ kGenIn V H :=
      (Subgroup.mem_normalizer_iff.mp hN (k : G)).mp k.2
    have hxA : a * (k : G) * a⁻¹ ∈ conjSubgroup A a⁻¹ :=
      (mem_conjSubgroup_iff (A := A) (g := a⁻¹) (x := a * (k : G) * a⁻¹)).mpr (by
        simpa [mul_assoc] using hkA)
    refine mem_barSub.mpr ⟨⟨a * (k : G) * a⁻¹, hxK⟩, hxA, ?_⟩
    exact (D.act ⟨a, ha⟩ k ⟨a * (k : G) * a⁻¹, hxK⟩ rfl).symm
  · intro hy
    obtain ⟨k, hkA, rfl⟩ := mem_barSub.mp hy
    have hk' : a⁻¹ * (k : G) * a ∈ A := by
      simpa only [inv_inv] using
        (mem_conjSubgroup_iff (A := A) (g := a⁻¹) (x := (k : G))).mp hkA
    have hk'K : a⁻¹ * (k : G) * a ∈ kGenIn V H := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) (k : G)).mp k.2
    refine mem_map.mpr ⟨ψ ⟨a⁻¹ * (k : G) * a, hk'K⟩,
      mem_barSub.mpr ⟨_, hk', rfl⟩, ?_⟩
    exact D.act ⟨a, ha⟩ ⟨a⁻¹ * (k : G) * a, hk'K⟩ k
      (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)

private theorem wc85fr_barSub_inf_T (D : RootData V H T S ψ ρ R Sy e) :
    barSub (kGenIn V H) ψ T = barSub (kGenIn V H) ψ (T ⊓ kGenIn V H) := by
  rw [barSub, barSub]
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩

private theorem wc85fr_map_rho_Sy (D : RootData V H T S ψ ρ R Sy e) {a : G} (ha : a ∈ H)
    (haT : a ∈ T) :
    Subgroup.map (ρ ⟨a, ha⟩).toMonoidHom Sy = Sy := by
  rw [← D.sylow, wc85fr_barSub_inf_T D]
  have hkN : a ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) :=
    D.hyp.le_normalizer_kGenIn_of_eq_sup D.eq_sup ha
  have hconj : conjSubgroup (T ⊓ kGenIn V H) a⁻¹ = T ⊓ kGenIn V H := by
    have hTa : T.map (MulAut.conj a).toMonoidHom = T := by
      simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer haT)
    have hKa : (kGenIn V H).map (MulAut.conj a).toMonoidHom = kGenIn V H := by
      simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp hkN
    rw [conjSubgroup, inv_inv, Subgroup.map_inf T (kGenIn V H)
      (MulAut.conj a).toMonoidHom (MulAut.conj a).injective, hTa, hKa]
  rw [wc85fr_map_rho_barSub D ha inf_le_right, hconj]

private theorem wc85fr_map_rho_R (D : RootData V H T S ψ ρ R Sy e) {a : G} (ha : a ∈ H)
    (haT : a ∈ T) :
    Subgroup.map (ρ ⟨a, ha⟩).toMonoidHom R = R := by
  rw [← D.root, wc85fr_map_rho_barSub D ha (le_kGenIn_self V H),
    conjSubgroup_eq_iff_mem_normalizer.mpr
      ((Subgroup.normalizer (V : Set G)).inv_mem (D.hyp.T_le_normalizer haT))]

private theorem wc85fr_map_rho_Pα {X₂ Pα : Subgroup S} (D : RootData V H T S ψ ρ R Sy e)
    (hP : RootParabolic R Sy X₂ Pα e) {a : G} (ha : a ∈ H) (haT : a ∈ T) :
    Subgroup.map (ρ ⟨a, ha⟩).toMonoidHom Pα = Pα :=
  hP.invariant (ρ ⟨a, ha⟩) (wc85fr_map_rho_Sy D ha haT) (wc85fr_map_rho_R D ha haT)

private theorem wc85fr_map_rho_Nα_le {X₂ Pα : Subgroup S} (D : RootData V H T S ψ ρ R Sy e)
    (hP : RootParabolic R Sy X₂ Pα e) {b : G} (hb : b ∈ H) (hbT : b ∈ T) :
    Subgroup.map (ρ ⟨b, hb⟩).toMonoidHom (Sy ⊓ Subgroup.normalizer (X₂ : Set S)) ≤
      Sy ⊓ Subgroup.normalizer (X₂ : Set S) := by
  haveI : Finite S := Finite.of_surjective ψ D.surj
  set Nα : Subgroup S := Sy ⊓ Subgroup.normalizer (X₂ : Set S) with hNα
  have hPα := wc85fr_map_rho_Pα D hP hb hbT
  have hle : Nα ≤ Pα := inf_le_left.trans hP.le
  have hle' : Subgroup.map (ρ ⟨b, hb⟩).toMonoidHom Nα ≤ Pα := by
    rw [← hPα]
    exact Subgroup.map_mono hle
  have hP' : Pα ≤ Subgroup.normalizer (Nα : Set S) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hP.normal
  have hnormal : ((Subgroup.map (ρ ⟨b, hb⟩).toMonoidHom Nα).subgroupOf Pα).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle', Subgroup.le_normalizer_iff]
    intro x hxP n hn
    rw [Subgroup.mem_map] at hn ⊢
    obtain ⟨m, hm, rfl⟩ := hn
    have hx' : (ρ ⟨b, hb⟩)⁻¹ x ∈ Pα := by
      have hxmem : x ∈ Subgroup.map (ρ ⟨b, hb⟩).toMonoidHom Pα := by rw [hPα]; exact hxP
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxmem
      rw [← hzx]
      simpa using hz
    refine ⟨(ρ ⟨b, hb⟩)⁻¹ x * m * ((ρ ⟨b, hb⟩)⁻¹ x)⁻¹, ?_, ?_⟩
    · exact ((Subgroup.mem_normalizer_iff.mp (hP' hx')) m).mp hm
    · simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.apply_inv_self]
  exact hP.largest _ hle' hnormal (hP.isPGroup.map (ρ ⟨b, hb⟩).toMonoidHom)

private theorem wc85fr_map_rho_Nα {X₂ Pα : Subgroup S} (D : RootData V H T S ψ ρ R Sy e)
    (hP : RootParabolic R Sy X₂ Pα e) {a : G} (ha : a ∈ H) (haT : a ∈ T) :
    Subgroup.map (ρ ⟨a, ha⟩).toMonoidHom (Sy ⊓ Subgroup.normalizer (X₂ : Set S)) =
      Sy ⊓ Subgroup.normalizer (X₂ : Set S) := by
  haveI : Finite S := Finite.of_surjective ψ D.surj
  refine Subgroup.eq_of_le_of_card_ge (wc85fr_map_rho_Nα_le D hP ha haT) ?_
  rw [Subgroup.card_map_of_injective (ρ ⟨a, ha⟩).injective]

private theorem wc85fr_mul_conj_mul_inv (φ : MulAut S) (g : S) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem wc85fr_mem_normalizer_InnNα {X₂ Pα : Subgroup S} {φ : MulAut S}
    (hφ : Subgroup.map φ.toMonoidHom (Sy ⊓ Subgroup.normalizer (X₂ : Set S)) =
      Sy ⊓ Subgroup.normalizer (X₂ : Set S)) :
    φ ∈ Subgroup.normalizer
      ((Sy ⊓ Subgroup.normalizer (X₂ : Set S)).map (MulAut.conj : S →* MulAut S) :
        Set (MulAut S)) := by
  set Nα : Subgroup S := Sy ⊓ Subgroup.normalizer (X₂ : Set S) with hNα
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj φ).toMonoidHom.comp (MulAut.conj : S →* MulAut S) =
      (MulAut.conj : S →* MulAut S).comp φ.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    exact wc85fr_mul_conj_mul_inv φ g
  change map ((MulEquiv.toMonoidHom (MulAut.conj φ)).comp (MulAut.conj : S →* MulAut S)) Nα =
    map (MulAut.conj : S →* MulAut S) Nα
  rw [hcomp, ← Subgroup.map_map, hφ]

private theorem wc85fr_mem_normalizer_wClos (D : RootData V H T S ψ ρ R Sy e) {n : G}
    (hn : ∀ g : G, conjSubgroup V g ≤ T → conjSubgroup V (g * n⁻¹) ≤ T) :
    n ∈ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
  have hle : conjSubgroup (E3.wClos V 0 T) n⁻¹ ≤ E3.wClos V 0 T := by
    rw [wClos_zero_eq_iSup D.hyp.elemAbelian]
    rw [show conjSubgroup (⨆ (g : G) (_ : conjSubgroup V g ≤ T), conjSubgroup V g) n⁻¹ =
        (⨆ (g : G) (_ : conjSubgroup V g ≤ T), conjSubgroup V g).map
          (MulAut.conj n).toMonoidHom from by rw [conjSubgroup, inv_inv]]
    rw [Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => ?_
    have hmap : (conjSubgroup V g).map (MulAut.conj n).toMonoidHom =
        conjSubgroup V (g * n⁻¹) := by
      rw [show (MulAut.conj n).toMonoidHom = (MulAut.conj (n⁻¹)⁻¹).toMonoidHom from by
        rw [inv_inv]]
      exact conjSubgroup_conjSubgroup V g n⁻¹
    rw [hmap]
    exact le_iSup₂_of_le (g * n⁻¹) (hn g hg) le_rfl
  have hconj : conjSubgroup (E3.wClos V 0 T) n⁻¹ = E3.wClos V 0 T := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [E3.card_conjSubgroup]
  simpa [inv_inv] using (Subgroup.normalizer (E3.wClos V 0 T : Set G)).inv_mem
    (conjSubgroup_eq_iff_mem_normalizer.mp hconj)

theorem wc85fr_T_le_normalizer_wClos (D : RootData V H T S ψ ρ R Sy e) :
    T ≤ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
  intro t ht
  refine wc85fr_mem_normalizer_wClos D (n := t) fun g hg => ?_
  rw [← conjSubgroup_conjSubgroup V g t⁻¹]
  have hmap : conjSubgroup (conjSubgroup V g) t⁻¹ =
      (conjSubgroup V g).map (MulAut.conj t).toMonoidHom := by
    rw [conjSubgroup, inv_inv]
  rw [hmap]
  exact (Subgroup.map_mono hg).trans (le_of_eq
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht)))

theorem wc85fr_mem_normalizer_of_psi (D : RootData V H T S ψ ρ R Sy e) {k : ↥(kGenIn V H)}
    (hk : ψ k ∈ Subgroup.normalizer (R : Set S)) :
    (k : G) ∈ Subgroup.normalizer (V : Set G) := by
  have hkH : (k : G) ∈ H := (kGenIn_le_H D.hyp.le_H) k.2
  have hbar : barSub (kGenIn V H) ψ (conjSubgroup V (k : G)⁻¹) =
      barSub (kGenIn V H) ψ (conjSubgroup V (1 : G)) := by
    rw [conjSubgroup_one, D.root]
    rw [show (k : G)⁻¹ = ((k⁻¹ : ↥(kGenIn V H)) : G) from
        (Subgroup.coe_inv (kGenIn V H) k).symm,
      barSub_conjSubgroup ψ V k⁻¹, map_inv, D.root]
    exact conjSubgroup_eq_iff_mem_normalizer.mpr
      ((Subgroup.normalizer (R : Set S)).inv_mem hk)
  have heq : conjSubgroup V (k : G)⁻¹ = conjSubgroup V (1 : G) :=
    wc85fx_conjSubgroup_eq_of_barSub_eq D (H.inv_mem hkH) H.one_mem hbar
  rw [conjSubgroup_one] at heq
  simpa [inv_inv] using (Subgroup.normalizer (V : Set G)).inv_mem
    (conjSubgroup_eq_iff_mem_normalizer.mp heq)

private theorem wc85fr_exists_mul_eq_of_mem_sup_of_le_normalizer {S N : Subgroup G}
    (hN : S ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ S ⊔ N) :
    ∃ s ∈ S, ∃ n ∈ N, s * n = x := by
  rw [sup_eq_closure] at hx
  refine closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, N.one_mem, by simp⟩
    · exact ⟨1, S.one_mem, x, hx, by simp⟩
  · exact ⟨1, S.one_mem, 1, N.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨s₁, hs₁, n₁, hn₁, rfl⟩ ⟨s₂, hs₂, n₂, hn₂, rfl⟩
    refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, (s₂⁻¹ * n₁ * s₂) * n₂,
      N.mul_mem (by simpa using (Subgroup.mem_normalizer_iff.mp (hN (S.inv_mem hs₂)) n₁).mp hn₁)
        hn₂, ?_⟩
    group
  · rintro _ _ ⟨s, hs, n, hn, rfl⟩
    refine ⟨s⁻¹, S.inv_mem hs, s * n⁻¹ * s⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hN hs) n⁻¹).mp (N.inv_mem hn), ?_⟩
    group

private theorem wc85fr_T_le_normalizer_P (D : RootData V H T S ψ ρ R Sy e) {X₂ Pα : Subgroup S}
    (hP : RootParabolic R Sy X₂ Pα e) :
    T ≤ Subgroup.normalizer (barPre (kGenIn V H) ψ Pα : Set G) := by
  intro t ht
  have htH : t ∈ H := D.hyp.T_le_H ht
  have htN : t ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) :=
    D.hyp.le_normalizer_kGenIn_of_eq_sup D.eq_sup htH
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxK, hψx⟩ := mem_barPre.mp hx
    have hxK' : t * x * t⁻¹ ∈ kGenIn V H :=
      (Subgroup.mem_normalizer_iff.mp htN x).mp hxK
    have hρ : Subgroup.map (ρ ⟨t, htH⟩).toMonoidHom Pα = Pα :=
      wc85fr_map_rho_Pα D hP htH ht
    refine mem_barPre.mpr ⟨hxK', ?_⟩
    have hact := D.act ⟨t, htH⟩ ⟨x, hxK⟩ ⟨t * x * t⁻¹, hxK'⟩ rfl
    rw [← hact]
    exact hρ ▸ Subgroup.mem_map.mpr ⟨ψ ⟨x, hxK⟩, hψx, rfl⟩
  · intro hx
    obtain ⟨hyK, hψy⟩ := mem_barPre.mp hx
    have htinvH : t⁻¹ ∈ H := H.inv_mem htH
    have htinvN : t⁻¹ ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) :=
      (Subgroup.normalizer _).inv_mem htN
    have hxK : x ∈ kGenIn V H := by
      have h := (Subgroup.mem_normalizer_iff.mp htinvN (t * x * t⁻¹)).mp hyK
      rwa [show t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x by group] at h
    refine mem_barPre.mpr ⟨hxK, ?_⟩
    have hρinv : Subgroup.map (ρ ⟨t⁻¹, htinvH⟩).toMonoidHom Pα = Pα :=
      wc85fr_map_rho_Pα D hP htinvH (T.inv_mem ht)
    have hact := D.act ⟨t⁻¹, htinvH⟩ ⟨t * x * t⁻¹, hyK⟩ ⟨x, hxK⟩ (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group)
    rw [← hact]
    exact hρinv ▸ Subgroup.mem_map.mpr ⟨ψ ⟨t * x * t⁻¹, hyK⟩, hψy, rfl⟩

private theorem wc85fr_isSylowIn_of_le_of_le {p : ℕ} {P K K' : Subgroup G} (hP : IsSylowIn p P K)
    (hPK' : P ≤ K') (hK'K : K' ≤ K) : IsSylowIn p P K' := by
  refine ⟨hPK', hP.isPGroup, fun h => hP.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P K' K hPK' hK'K]
  exact h.mul_right _

theorem wc85fr_factor (D : RootData V H T S ψ ρ R Sy e) {X₂ Pα : Subgroup S}
    (hP : RootParabolic R Sy X₂ Pα e)
    (hinner : ∀ U : Subgroup G, (∃ g : G, U = conjSubgroup V g) → U ≤ T → ∀ (u : G), u ∈ U →
      ∀ huH : u ∈ H, ∃ g ∈ Sy ⊓ Subgroup.normalizer (X₂ : Set S), ρ ⟨u, huH⟩ = MulAut.conj g) :
    ∀ x ∈ barPre (kGenIn V H) ψ Pα ⊔ T, ∃ y ∈ barPre (kGenIn V H) ψ Pα ⊔ T,
      ∃ n ∈ barPre (kGenIn V H) ψ Pα ⊔ T, x = y * n ∧
        (∃ hyH : y ∈ H, ∃ g ∈ Sy ⊓ Subgroup.normalizer (X₂ : Set S),
          ρ ⟨y, hyH⟩ = MulAut.conj g) ∧
        n ∈ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
  intro x hx
  let P : Subgroup G := barPre (kGenIn V H) ψ Pα
  let Nα : Subgroup S := Sy ⊓ Subgroup.normalizer (X₂ : Set S)
  let Inn : Subgroup (MulAut S) := Nα.map (MulAut.conj : S →* MulAut S)
  let Z : Subgroup G := (Inn.comap ρ).map H.subtype
  let Y : Subgroup G := (P ⊔ T) ⊓ Z
  have hPK : P ≤ kGenIn V H := barPre_le (kGenIn V H) ψ Pα
  have hPH : P ≤ H := hPK.trans (kGenIn_le_H D.hyp.le_H)
  have hTH : T ≤ H := D.hyp.T_le_H
  have hPTH : P ⊔ T ≤ H := sup_le hPH hTH
  have hYle : Y ≤ P ⊔ T := inf_le_left
  have hYH : Y ≤ H := hYle.trans hPTH
  have hTP : T ≤ Subgroup.normalizer (P : Set G) := wc85fr_T_le_normalizer_P D hP
  have keyPT : ∀ (u : G) (hu : u ∈ P ⊔ T),
      ρ ⟨u, hPTH hu⟩ ∈ Subgroup.normalizer (Inn : Set (MulAut S)) := by
    intro u hu
    have huTP : u ∈ T ⊔ P := by rwa [sup_comm] at hu
    obtain ⟨t, htT, p, hpP, htp⟩ :=
      wc85fr_exists_mul_eq_of_mem_sup_of_le_normalizer hTP huTP
    have hρp : ρ ⟨p, hPH hpP⟩ ∈ Subgroup.normalizer (Inn : Set (MulAut S)) := by
      have hψp : ψ ⟨p, hPK hpP⟩ ∈ Pα := (mem_barPre.mp hpP).2
      have hle : Nα ≤ Pα := inf_le_left.trans hP.le
      have hPN : Pα ≤ Subgroup.normalizer (Nα : Set S) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hP.normal
      have hφ : Subgroup.map (MulAut.conj (ψ ⟨p, hPK hpP⟩)).toMonoidHom Nα = Nα :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPN hψp)
      rw [wc85fr_rho_eq_conj_psi D ⟨p, hPK hpP⟩]
      exact wc85fr_mem_normalizer_InnNα (Pα := Pα) hφ
    have hρt : ρ ⟨t, hTH htT⟩ ∈ Subgroup.normalizer (Inn : Set (MulAut S)) :=
      wc85fr_mem_normalizer_InnNα (Pα := Pα) (wc85fr_map_rho_Nα D hP (hTH htT) htT)
    have huH : u ∈ H := hPTH hu
    have hu_eq : (⟨u, huH⟩ : ↥H) = ⟨t, hTH htT⟩ * ⟨p, hPH hpP⟩ :=
      Subtype.ext (by simpa only [Subgroup.coe_mul] using htp.symm)
    rw [hu_eq, map_mul]
    exact (Subgroup.normalizer _).mul_mem hρt hρp
  have hYnormal : (Y.subgroupOf (P ⊔ T)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYle, Subgroup.le_normalizer_iff]
    intro u huPT y hyY
    have huH : u ∈ H := hPTH huPT
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (P ⊔ T).mul_mem ((P ⊔ T).mul_mem huPT hyY.1) ((P ⊔ T).inv_mem huPT)
    · obtain ⟨h, hhInn, hhy⟩ := Subgroup.mem_map.mp hyY.2
      have hhInn' : ρ h ∈ Inn := Subgroup.mem_comap.mp hhInn
      refine Subgroup.mem_map.mpr ⟨⟨u, huH⟩ * h * ⟨u, huH⟩⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hρu : ρ ⟨u, huH⟩ ∈ Subgroup.normalizer (Inn : Set (MulAut S)) := keyPT u huPT
        have := (Subgroup.mem_normalizer_iff.mp hρu (ρ h)).mp hhInn'
        simpa only [map_mul, map_inv] using this
      · simp only [map_mul, map_inv, hhy]
        rfl
  have hTsyl : IsSylowIn 2 T (P ⊔ T) :=
    wc85fr_isSylowIn_of_le_of_le D.hyp.sylow_H le_sup_right hPTH
  have hRTsyl : IsSylowIn 2 (T ⊓ Y) Y := IsSylowIn.inf_normal hTsyl hYle hYnormal
  have hgenY : ∀ g : G, conjSubgroup V g ≤ T → conjSubgroup V g ≤ Y := by
    intro g hg
    refine le_inf (hg.trans le_sup_right) ?_
    intro u hu
    have huH : u ∈ H := hPTH ((le_sup_right : T ≤ P ⊔ T) (show u ∈ T from hg hu))
    obtain ⟨g', hg'N, hρu⟩ := hinner (conjSubgroup V g) ⟨g, rfl⟩ hg u hu huH
    refine Subgroup.mem_map.mpr ⟨⟨u, huH⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_map.mpr ⟨g', hg'N, hρu.symm⟩
  obtain ⟨y, hyY, n, hnPT, hnN, hyn⟩ := frattini_isSylowIn hYle hYnormal hRTsyl x hx
  obtain ⟨hh, hhInn, hhy⟩ := Subgroup.mem_map.mp hyY.2
  obtain ⟨g, hgN, hg_eq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hhInn)
  have hyH : y ∈ H := by
    rw [← hhy]
    exact hh.2
  refine ⟨y, hYle hyY, n, hnPT, hyn.symm, ⟨hyH, g, hgN, ?_⟩, ?_⟩
  · rw [hg_eq]
    exact congrArg ρ (Subtype.ext hhy.symm)
  · refine wc85fr_mem_normalizer_wClos D (n := n) fun g₀ hg₀ => ?_
    have hg₀RT : conjSubgroup V g₀ ≤ T ⊓ Y := le_inf hg₀ (hgenY g₀ hg₀)
    calc conjSubgroup V (g₀ * n⁻¹) = conjSubgroup (conjSubgroup V g₀) n⁻¹ :=
          (conjSubgroup_conjSubgroup V g₀ n⁻¹).symm
      _ ≤ conjSubgroup (T ⊓ Y) n⁻¹ := E3.conjSubgroup_mono_left n⁻¹ hg₀RT
      _ = T ⊓ Y := by
          have h := E3.conjSubgroup_conj_inv (T ⊓ Y) n
          rw [conjSubgroup_eq_iff_mem_normalizer.mpr hnN] at h
          exact h
      _ ≤ T := inf_le_left

theorem wc85fr_false (D : RootData V H T S ψ ρ R Sy e) {X₂ Pα : Subgroup S}
    (hP : RootParabolic R Sy X₂ Pα e)
    (hinner : ∀ U : Subgroup G, (∃ g : G, U = conjSubgroup V g) → U ≤ T → ∀ (u : G), u ∈ U →
      ∀ huH : u ∈ H, ∃ g ∈ Sy ⊓ Subgroup.normalizer (X₂ : Set S), ρ ⟨u, huH⟩ = MulAut.conj g)
    (hno : ∀ k : ↥(kGenIn V H), (k : G) ∈ Subgroup.normalizer (E3.wClos V 0 T : Set G) →
      (k : G) ∈ Subgroup.normalizer (V : Set G)) : False := by
  let P : Subgroup G := barPre (kGenIn V H) ψ Pα
  have hPK : P ≤ kGenIn V H := barPre_le (kGenIn V H) ψ Pα
  have hPH : P ≤ H := hPK.trans (kGenIn_le_H D.hyp.le_H)
  have hPTH : P ⊔ T ≤ H := sup_le hPH D.hyp.T_le_H
  have key : ∀ (x : G) (hxP : x ∈ P),
      ψ ⟨x, hPK hxP⟩ ∈ Subgroup.normalizer (R : Set S) := by
    intro x hxP
    have hxK : x ∈ kGenIn V H := hPK hxP
    have hxH : x ∈ H := kGenIn_le_H D.hyp.le_H hxK
    obtain ⟨y, hyPT, n, hnPT, hxy, hyInner, hnW⟩ :=
      wc85fr_factor D hP hinner x (Subgroup.mem_sup_left hxP)
    obtain ⟨hyH, g, hgN, hρy⟩ := hyInner
    have hnTP : n ∈ T ⊔ P := by rwa [sup_comm] at hnPT
    obtain ⟨t, htT, k', hk'P, htk'⟩ :=
      wc85fr_exists_mul_eq_of_mem_sup_of_le_normalizer (wc85fr_T_le_normalizer_P D hP) hnTP
    have hk'K : k' ∈ kGenIn V H := hPK hk'P
    have hk'W : k' ∈ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
      rw [show k' = t⁻¹ * n by rw [← htk']; group]
      exact (Subgroup.normalizer _).mul_mem
        ((Subgroup.normalizer _).inv_mem (wc85fr_T_le_normalizer_wClos D htT)) hnW
    have hk'V : k' ∈ Subgroup.normalizer (V : Set G) := hno ⟨k', hk'K⟩ hk'W
    have hnV : n ∈ Subgroup.normalizer (V : Set G) := by
      rw [← htk']
      exact (Subgroup.normalizer _).mul_mem (D.hyp.T_le_normalizer htT) hk'V
    have hnH : n ∈ H := hPTH hnPT
    have hρn : Subgroup.map (ρ ⟨n, hnH⟩).toMonoidHom R = R := by
      rw [← D.root, wc85fr_map_rho_barSub D hnH (le_kGenIn_self V H),
        conjSubgroup_eq_iff_mem_normalizer.mpr
          ((Subgroup.normalizer (V : Set G)).inv_mem hnV)]
    have hρyR : Subgroup.map (ρ ⟨y, hyH⟩).toMonoidHom R = R := by
      rw [hρy]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (D.sylow_normalizes.2.2 hgN.1)
    have hx_eq : (⟨x, hxH⟩ : ↥H) = ⟨y, hyH⟩ * ⟨n, hnH⟩ :=
      Subtype.ext (by simpa only [Subgroup.coe_mul] using hxy)
    have hρxR : Subgroup.map (ρ ⟨x, hxH⟩).toMonoidHom R = R := by
      rw [hx_eq, map_mul]
      rw [show ((ρ ⟨y, hyH⟩) * (ρ ⟨n, hnH⟩)).toMonoidHom =
          (ρ ⟨y, hyH⟩).toMonoidHom.comp (ρ ⟨n, hnH⟩).toMonoidHom from rfl]
      rw [← Subgroup.map_map, hρn, hρyR]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← wc85fr_rho_eq_conj_psi D ⟨x, hxK⟩]
    exact hρxR
  exact hP.not_le fun a ha => by
    obtain ⟨k, hk⟩ := D.surj a
    have hkP : (k : G) ∈ P := by
      refine mem_barPre.mpr ⟨k.2, ?_⟩
      rwa [hk]
    have h := key (k : G) hkP
    have hψ : ψ ⟨(k : G), hPK hkP⟩ = a := by
      have : (⟨(k : G), hPK hkP⟩ : ↥(kGenIn V H)) = k := Subtype.ext rfl
      rw [this, hk]
    rwa [hψ] at h

theorem wc85fr_eq_of_exists (D : RootData V H T S ψ ρ R Sy e)
    (hmax : ∀ M : Subgroup S, Subgroup.normalizer (R : Set S) ≤ M →
      M = Subgroup.normalizer (R : Set S) ∨ M = ⊤)
    (hk : ∃ k : ↥(kGenIn V H), (k : G) ∈ Subgroup.normalizer (E3.wClos V 0 T : Set G) ∧
      (k : G) ∉ Subgroup.normalizer (V : Set G)) :
    H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
      (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) := by
  obtain ⟨k₀, hkW, hkM⟩ := hk
  let Ksub : Subgroup G := kGenIn V H
  let J : Subgroup G := (Ksub ⊓ Subgroup.normalizer (V : Set G)) ⊔
    (Ksub ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G))
  have hJK : J ≤ Ksub := sup_le inf_le_left inf_le_left
  let A : Subgroup S := (J.subgroupOf Ksub).map ψ
  have hNA : Subgroup.normalizer (R : Set S) ≤ A := by
    intro s hs
    obtain ⟨k₁, rfl⟩ := D.surj s
    have hk₁M : (k₁ : G) ∈ Subgroup.normalizer (V : Set G) :=
      wc85fr_mem_normalizer_of_psi D hs
    refine Subgroup.mem_map.mpr ⟨k₁, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨k₁.2, hk₁M⟩))
  have hkA : ψ k₀ ∈ A := by
    refine Subgroup.mem_map.mpr ⟨k₀, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨k₀.2, hkW⟩))
  have hnotN : ψ k₀ ∉ Subgroup.normalizer (R : Set S) := fun h =>
    hkM (wc85fr_mem_normalizer_of_psi D h)
  have hAtop : A = ⊤ := by
    rcases hmax A hNA with h | h
    · exact absurd (h ▸ hkA) hnotN
    · exact h
  have hKJ : Ksub ≤ J := by
    intro x hxK
    let k'' : ↥Ksub := ⟨x, hxK⟩
    have hk''A : ψ k'' ∈ A := by rw [hAtop]; exact Subgroup.mem_top _
    obtain ⟨j, hjJ, hjψ⟩ := Subgroup.mem_map.mp hk''A
    have hjGJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hjJ
    let d : ↥Ksub := k'' * j⁻¹
    have hdψ : ψ d = 1 := by rw [map_mul, map_inv, hjψ, mul_inv_cancel]
    have hdM : (d : G) ∈ Subgroup.normalizer (V : Set G) :=
      wc85fr_mem_normalizer_of_psi D (by rw [hdψ]; exact Subgroup.one_mem _)
    have hdJ : (d : G) ∈ J :=
      Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨d.2, hdM⟩)
    have hdj : (d : G) * (j : G) = x := by
      change x * (j : G)⁻¹ * (j : G) = x
      group
    rw [← hdj]
    exact J.mul_mem hdJ hjGJ
  have hKH : Ksub ≤ H := kGenIn_le_H D.hyp.le_H
  have hJle : J ≤ (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
      (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) := by
    refine sup_le ?_ ?_
    · exact le_trans (inf_le_inf_right (Subgroup.normalizer (V : Set G)) hKH) le_sup_left
    · exact le_trans (inf_le_inf_right (Subgroup.normalizer (E3.wClos V 0 T : Set G)) hKH)
        le_sup_right
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  conv_lhs => rw [D.eq_sup]
  refine sup_le (hKJ.trans hJle) ?_
  exact le_trans (le_inf D.hyp.T_le_H D.hyp.T_le_normalizer) le_sup_left

theorem rootData_frattini (D : RootData V H T S ψ ρ R Sy e) {X₂ Pα : Subgroup S}
    (hP : RootParabolic R Sy X₂ Pα e)
    (hinner : ∀ U : Subgroup G, (∃ g : G, U = conjSubgroup V g) → U ≤ T → ∀ (u : G), u ∈ U →
      ∀ huH : u ∈ H, ∃ g ∈ Sy ⊓ Subgroup.normalizer (X₂ : Set S), ρ ⟨u, huH⟩ = MulAut.conj g) :
    H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
      (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) := by
  have hex : ∃ k : ↥(kGenIn V H), (k : G) ∈ Subgroup.normalizer (E3.wClos V 0 T : Set G) ∧
      (k : G) ∉ Subgroup.normalizer (V : Set G) := by
    by_contra hno
    exact wc85fr_false D hP hinner fun k hk => by
      by_contra hkV
      exact hno ⟨k, hk, hkV⟩
  exact wc85fr_eq_of_exists D hP.maximal hex

end RootData

end CFSG.LocalAnalysis.WeakClosure81

end
