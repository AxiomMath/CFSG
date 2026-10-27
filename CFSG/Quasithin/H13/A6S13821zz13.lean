module

public import CFSG.Quasithin.H13.A6S13821zz12
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases1
public import CFSG.Quasithin.H13.A6S13821zz11

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem fixProp_of_component (hA21 : AsA21SQTKSection) (hB51 : AsB51) {V : Type} [CommGroup V]
    [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hq : CFSG.IsQuasisimple ↥L)
    {Bb : Subgroup (MulAut V)} (hBG : Bb ≤ G) (hFF : IsFFModule Bb)
    (hfaith : ∀ a ∈ Bb, (∀ l ∈ L, a * l = l * a) → a = 1)
    {X : Type} [Group X] [Finite X] (hSQ : SQTKGroup X) (κ : X →* ↥L)
    (hκ : Function.Surjective κ) (N : Subgroup X) [N.Normal] (hperf : commutator (X ⧸ N) = ⊤)
    (hs : IsSimpleGroup ((X ⧸ N) ⧸ Subgroup.center (X ⧸ N))) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card ((X ⧸ N) ⧸ Subgroup.center (X ⧸ N)) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)))
    (hoddZ : Odd (Nat.card (Subgroup.center (X ⧸ N)))) {T₀ : Subgroup X}
    (hsyl : IsSylowTwoOf T₀ ⊤) (hNT : N ≤ T₀) (hO : ∀ x ∈ N, κ x = 1) :
    S1565.FixProp (L.subtype.comp κ) (Subgroup.normalizer (T₀ : Set X)) ⊥ ⊤ := by
  classical
  have hLo : CFSG.Open.IsQuasisimple ↥L := Insp9.open_of_isQuasisimple hq
  have : Group.IsPerfect ↥L := hq.1
  have : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLo
  have hLnG : (L.subgroupOf G).Normal := ⟨fun l hl g => by
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact hLn _ g.2 _ hl⟩
  have hL : CFSG.Open.IsComponentOf L G :=
    ⟨hLG, IsSubnormal.step hLG hLnG (IsSubnormal.refl G), hLo⟩
  obtain ⟨A, hA'⟩ := B6.exists_isFFStarOffender hFF
  have hA : IsFFStarOffender G A := ⟨hA'.1.trans hBG, hA'.2.1, hA'.2.2.1, hA'.2.2.2⟩
  have hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := fun a ha =>
    Subgroup.mem_normalizer_fintype fun l hl => hLn a (hA.1 ha) l hl
  have hLA : ⁅L, A⁆ = L :=
    commutator_eq_of_faithful hq hAL (fun a ha => hfaith a (hA'.1 ha)) hA.2.1
  obtain ⟨hH₀n, -, -, hst, -, -⟩ := FFC.B59.red_basic hV2 hL hA hLA
  obtain ⟨hO2b, hFb, hLbq, hLbH, -, -, hoff, hcomm, hsup⟩ := FFC.B59.red_aut hV2 hL hA hLA
  have hLU : L ≤ CFSG.Quasithin.stabSub (FFC.B59.W0 L A) := le_sup_left.trans hst
  have hmem : ∀ l : ↥L, resHomOn (FFC.B59.W0 L A) hLU l ∈ FFC.B59.Kr L A := fun l =>
    mem_autSub.mpr ⟨⟨l, hLU l.2⟩, l.2, rfl⟩
  set ρ : ↥L →* ↥(FFC.B59.Kr L A) := (resHomOn (FFC.B59.W0 L A) hLU).codRestrict _ hmem with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hgL, rfl⟩ := mem_autSub.mp hφ
    exact ⟨⟨g, hgL⟩, rfl⟩
  set κ' : X →* ↥(FFC.B59.Kr L A) := ρ.comp κ with hκ'
  have hκ's : Function.Surjective κ' := hρs.comp hκ
  have hKrq : CFSG.IsQuasisimple ↥(FFC.B59.Kr L A) := B1Red.isQuasisimple_of_open hLbq
  have : Nontrivial ↥(FFC.B59.Kr L A) := CFSG.ComponentClassification.Quasisimple.nontrivial hLbq
  have hSQr : SQTKGroup ↥(FFC.B59.Kr L A) := by
    have hlayer : CFSG.layer ↥(⊤ : Subgroup ↥(FFC.B59.Kr L A)) = ⊤ :=
      B5.layer_eq_top_of_quasisimple
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hKrq)
    have h2 : IsPGroup 2 (↥(FFC.B59.Kr L A) ⧸ (⊤ : Subgroup ↥(FFC.B59.Kr L A))) := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨0, ?_⟩
      rw [pow_zero, pow_one, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_top _
    exact hA21 X hSQ ⊤ ↥(FFC.B59.Kr L A) (κ'.comp (⊤ : Subgroup X).subtype)
      (fun y => by
        obtain ⟨x, hx⟩ := hκ's y
        exact ⟨⟨x, Subgroup.mem_top x⟩, hx⟩) ⊤ hlayer h2
  have hZ : centerOf (FFC.B59.Xr L A) ≤ FFC.B59.Kr L A := hFb ▸ FFC.B59.centerOf_le_genFitting _
  have hKJ : FFC.B59.Kr L A ≤ ffJ (FFC.B59.Xr L A) := B1Red.K_le_ffJ hLbH hoff hcomm
  have hJ : FFC.B59.Xr L A = ffJ (FFC.B59.Xr L A) :=
    le_antisymm (hsup.le.trans (sup_le hKJ (B6.le_ffJ hoff))) (B6.ffJ_le _)
  have hV2' : ∀ w : ↥(FFC.B59.W0 L A), w ^ 2 = 1 := fun w => Subtype.ext (hV2 w)
  have hc := hB51 ↥(FFC.B59.W0 L A) hV2' (FFC.B59.Xr L A) (FFC.B59.Kr L A)
    ⟨by rw [hFb, sup_eq_left.2 hZ], hKrq, hSQr, hLbH, hO2b, hJ⟩
  have hO' : ∀ x ∈ N, κ' x = 1 := fun x hx => by
    rw [hκ', MonoidHom.comp_apply, hO x hx, map_one]
  have h0 := fixProp_of_b51 hV2' hc κ' hκ's N hperf hs hn hcard hoddZ hsyl hNT hO'
  have h0' : S1565.FixProp (L.subtype.comp κ) (Subgroup.normalizer (T₀ : Set X)) ⊥
      (fixV (pCoreOf 2 (L ⊔ A))) := by
    intro w hw hwB x _
    have hact : ∀ y : X, ((FFC.B59.Kr L A).subtype.comp κ' y) ⟨w, hw⟩ =
        ⟨(L.subtype.comp κ y) w, hLU (κ y).2 w |>.mpr hw⟩ := fun y => rfl
    have h1 : S1565.FixMod ((FFC.B59.Kr L A).subtype.comp κ') (Subgroup.normalizer (T₀ : Set X))
        ⊥ ⟨w, hw⟩ := by
      intro b hb
      have h2 : (L.subtype.comp κ b) w * w⁻¹ ∈ (⊥ : Subgroup V) := hwB b hb
      rw [Subgroup.mem_bot] at h2 ⊢
      rw [hact b]
      exact Subtype.ext h2
    have h3 := h0 ⟨w, hw⟩ (Subgroup.mem_top _) h1 x (Subgroup.mem_top x)
    rw [Subgroup.mem_bot, hact x] at h3
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h3
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ A)) := pCoreOf_isPGroup 2 (L ⊔ A)
  have hQL : ∀ q ∈ pCoreOf 2 (L ⊔ A), ∀ l ∈ L, q * l = l * q := by
    refine B1Red.commute_of_normal_not_le hLo
      (fun q hq l hl => hH₀n q (pCoreOf_le 2 (L ⊔ A) hq) l hl)
      (fun l hl q hq => B1Red.conj_mem_pCoreOf (Subgroup.mem_sup_left hl) hq) ?_
    intro hle
    exact Group.IsPerfect.not_isNilpotent ↥L (hQ2.to_le hle).isNilpotent
  have hBodd : Odd (Subgroup.normalizer (T₀ : Set X)).index := by
    have h1 : (Subgroup.normalizer (T₀ : Set X)).index ∣ T₀.index :=
      Subgroup.index_dvd_of_le Subgroup.le_normalizer
    have h2 : ¬ 2 ∣ T₀.index := by
      have h3 : ¬ 2 ∣ T₀.relIndex ⊤ := hsyl.2.2
      rwa [Subgroup.relIndex_top_right] at h3
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => h2 (h.trans h1))
  exact fixProp_top_of_fixV (L.subtype.comp κ) hV2 _ hBodd hQ2
    (fun q hq x => hQL q hq _ (κ x).2) h0'

end CFSG.Quasithin.H13.A6.A6S20
