module

public import CFSG.Milestones.ASVolI.D3a
public import CFSG.Quasithin.Vol2.Ch3D310Holds
public import CFSG.Quasithin.Background.RonanD35FF
public import CFSG.Quasithin.Background.RonanD38
public import CFSG.Quasithin.Background.RonanD39One
public import CFSG.Quasithin.Background.RonanD39Two
public import CFSG.Quasithin.Background.RonanD39LLt
public import CFSG.Quasithin.Background.D36AsmHolds
public import CFSG.Quasithin.Background.F918M8
public import CFSG.Quasithin.Background.D36GluedA5Holds
import CFSG.Quasithin.Background.RonanD37Main
import CFSG.Quasithin.Background.RonanD321
public import CFSG.Milestones.ASVolI.D2

public section

namespace CFSG.ASVolI.ChD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

@[expose] def IsCompOf (K M : Subgroup (MulAut W)) : Prop :=
  K ∈ cComp M ∧ CFSG.IsQuasisimple ↥K

@[expose] def IsSuzukiGp (K : Subgroup (MulAut W)) : Prop :=
  ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n

@[expose] def oThreeRes (M : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  ⨆ (p : ℕ) (_ : p.Prime) (_ : p ≠ 3), pCoreOf p M

@[expose] def HasChiefSeries (L : Subgroup (MulAut W)) (C : Subgroup W) (n : ℕ) : Prop :=
  ∃ N : Fin (n + 1) → Subgroup W, N 0 = C ∧ N (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, XMod.IsInv ↥L (N i.castSucc) ∧ XMod.IsInv ↥L (N i.succ) ∧
      XMod.IsIrrSec ↥L (N i.castSucc) (N i.succ)

@[expose] def D310TwoIn (T L : Subgroup (MulAut W)) (V Y : Subgroup W) : Prop :=
  ((∃ n, BinaryNaturalSL L V (V ⊓ fixV L) 3 n) ∨ (∃ n, BinaryNaturalSp4 L V (V ⊓ fixV L) n) ∨
      AlternatingNatural L V (V ⊓ fixV L) 6 ∨ BinaryNaturalSL L V (V ⊓ fixV L) 4 1 ∨
      BinaryNaturalSL L V (V ⊓ fixV L) 5 1 ∨ A7Four L V ⊥) ∧
    (∃ t ∈ T, t ∉ stabSub V) ∧
    ∀ t ∈ T, t ∉ stabSub V →
      IsSumMod (Y ⊓ fixV L) V (V.map t.toMonoidHom) Y ∧
        ¬ SecIsoL L V (V ⊓ fixV L) (V.map t.toMonoidHom) (V.map t.toMonoidHom ⊓ fixV L)

@[expose] def D38Concl2 {W : Type} [CommGroup W] [Finite W] (Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W) (n : ℕ) : Prop :=
  BinaryNaturalSz L V (V ⊓ fixV L) n ∧
  IsSumMod (orbSup T V ⊓ fixV Mp) V (V.map t.toMonoidHom) (orbSup T V) ∧
  V = commSub (orbSup T V) L ∧ V ≤ fixV (conjAutSub t L) ∧
  fixV (conjAutSub t L) ⊓ orbSup T V = V ⊔ (orbSup T V ⊓ fixV Mp)

@[expose] def D36Concl3 {W : Type} [CommGroup W] [Finite W] (Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W) : Prop :=
  (∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) ∧
  (IsSumMod (orbSup T V ⊓ fixV Mp) (commSub (orbSup T V) L)
      ((commSub (orbSup T V) L).map t.toMonoidHom) (orbSup T V) ∧
    ∀ u ∈ commSub (orbSup T V) L, ∀ g ∈ conjAutSub t L, g u = u) ∧
  ((∀ A : Subgroup (MulAut W), A ≤ T →
      autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
        A ≤ stabSub (commSub (orbSup T V) L)) ∧
    qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ)) ∧
  (commSub (orbSup T V) L = V ∨
    (IsPSL 3 2 1 ↥(autSub L (orbSup T V)) ∧
      (∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧ s ∉ stabSub V) ∧
      (∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) → s ∉ stabSub V →
        commSub (orbSup T V) L = V ⊔ V.map s.toMonoidHom ∧
          IsSumMod (commSub (orbSup T V) L ⊓ fixV Mp) V (V.map s.toMonoidHom)
            (commSub (orbSup T V) L)) ∧
      Nat.card ↥V = 2 ^ 3 * Nat.card ↥(V ⊓ fixV Mp)))

end CFSG.ASVolI.ChD

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChD

@[expose] def D_3_6 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → V < orbSup T V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      Mp = L ⊔ conjAutSub t L →
        D36Concl3 Mp T L V t ∨ D36Concl3 Mp T (conjAutSub t L) V t⁻¹

section D36


theorem as_D_3_6
    : D_3_6 := by
  have hL38 : CFSG.Quasithin.D3L38 := CFSG.Quasithin.d3L38_of_a38 CFSG.Quasithin.d3A38_holds
  have hA : CFSG.Quasithin.D36Acts :=
    CFSG.Quasithin.d36Acts_of_glued (CFSG.Quasithin.d36ActsGlued_of_L38 hL38)
  have h35 : CFSG.Quasithin.D35 := CFSG.Quasithin.H13.d35_proved
  have hA38 : CFSG.Quasithin.D36A38 := CFSG.Quasithin.d36A38_holds
  intro W _ _ M Mp T L V hD hlt t ht htn hMp
  rcases CFSG.Quasithin.d36Asm_holds h35 hA hA38 hL38 W M Mp T L V hD hlt t ht htn hMp with
    ⟨⟨c0, c1, c2, c3⟩, a⟩ | ⟨⟨c0, c1, c2, c3⟩, a⟩
  · exact Or.inl ⟨c0, c1, ⟨a, c2⟩, c3⟩
  · exact Or.inr ⟨c0, c1, ⟨a, c2⟩, c3⟩

end D36

@[expose] def D_3_7 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → V = orbSup T V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      Mp = L ⊔ conjAutSub t L →
      ∀ A : Subgroup (MulAut ↥V), A ∈ QhatStar (autSub T V) →
        (∃ n : ℕ, IsPSL 2 2 n ↥(autSub L V) ∧ Omega4PlusModule (autSub Mp V) n ∧
          ((qhatOf (autSub (Mp ⊔ T) V) = ((3 / 2 : ℚ) : WithTop ℚ) ∧
              (rk A = 2 * n ∨ (n = 3 ∧ rk A = 4))) ∨
            (n = 2 ∧ rk A = 3 ∧ qhatOf (autSub (Mp ⊔ T) V) = ((4 / 3 : ℚ) : WithTop ℚ)))) ∨
        (IsPSL 3 2 1 ↥(autSub L V) ∧ TensorNatL32 (autSub Mp V) ∧
          qhatOf (autSub (Mp ⊔ T) V) = ((5 / 4 : ℚ) : WithTop ℚ) ∧ rk A = 4)

section D37


theorem as_D_3_7
    : D_3_7 :=
  CFSG.Quasithin.RonanD37.d37_full

end D37

@[expose] def D_3_8 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → ∀ n : ℕ, CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n →
      qhatOf (autSub (Mp ⊔ T) (orbSup T V)) = ((2 : ℚ) : WithTop ℚ) ∧
      (∀ A : Subgroup (MulAut W), A ≤ T →
        autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) → A ≤ stabSub V) ∧
      ((Mp = L ∧ orbSup T V = V ∧ BinaryNaturalSz L V (V ⊓ fixV L) n) ∨
        (∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) ∧ Mp = L ⊔ conjAutSub t L ∧
          (D38Concl2 Mp T L V t n ∨ D38Concl2 Mp T (conjAutSub t L) V t⁻¹ n)))

section D38


theorem as_D_3_8
    : D_3_8 := by
  intro W _ _ M Mp T L V hD n hsz
  exact RonanD38.d38_main W M Mp T L V hD n hsz

end D38

@[expose] def D_3_9 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
    (V = orbSup T V ∨ (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L)) →
    ∀ A ∈ QhatStar M,
      ((∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) →
        (orbSup T V = ⊤ ∨
          (V = orbSup T V ∧ Mp = L ∧ IsFFModule (autSec (L ⊔ T) V (fixV Mp)) ∧
            ∀ r : ℚ, qhatOf (autSec (L ⊔ T) V (fixV Mp)) = (r : WithTop ℚ) →
              ∃ n : ℕ, HasChiefSeries L (fixV Mp) n ∧ (n : ℚ) * r ≤ 2))) ∧
      (¬ (∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) →
        (∃ X : Subgroup (MulAut W), X ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) ∧
            (∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X) ∧
            X = cmt X (A ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) ∧
            ((∃ K : Subgroup (MulAut W), IsCompOf K M ∧ ¬ IsSuzukiGp K ∧ X = conjClosure K A) ∨
              (X ≤ pCoreOf 3 M ∧ Nat.card ↥X = 3))) ∧
        Mp = L ∧ (∀ a ∈ A, ∀ y ∈ oThreeRes M, a * y = y * a) ∧
        (∀ K : Subgroup (MulAut W), K ∈ cComp (M ⊓ Subgroup.centralizer (L : Set (MulAut W))) →
          CFSG.IsQuasisimple ↥K → IsSuzukiGp K → ∀ a ∈ A, ∀ y ∈ K, a * y = y * a))

section D39


theorem as_D_3_9
    : D_3_9 := by
  intro W _ _ M Mp T L V hD hqM hcase A hA
  rcases CFSG.Quasithin.H13.d38_mp_cases CFSG.Quasithin.Vol2.Ch10.SecA.a38ForSQTKCat_proved hD.hyp
    with hMp | ⟨t, htT, htn, hMp⟩
  · exact ⟨fun hAf => RonanD39.d39_one_L hD hMp hqM hcase hA hAf,
      fun hnf => RonanD39.d39_two_L hD hMp hqM hcase hA hnf⟩
  · obtain ⟨htop, hfaith⟩ := RonanD39.d39_llt hD hqM hcase htT htn hMp
    refine ⟨fun _ => Or.inl htop, fun hnf => (hnf fun a ha hac => ?_).elim⟩
    have hmem : a ∈ A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) :=
      ⟨ha, Subgroup.mem_centralizer_iff.2 fun x hx => (hac x hx).symm⟩
    rw [hfaith A hA, Subgroup.mem_bot] at hmem
    exact hmem

end D39

@[expose] def D_3_10 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → Mp = L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
      ((∀ t ∈ T, t ∈ stabSub V) ∧ V = orbSup T V) ∨ D310TwoIn T L V ⊤

section A7Cohomology


theorem a7Four_fixV_eq_bot {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {V : Subgroup W} (hinv : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V)
    (hcomm : commSub V L = V) (h : A7Four L V (V ⊓ fixV L)) : V ⊓ fixV L = ⊥ := by
  obtain ⟨α, π₀, hπs₀, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  let π : ↥(alternatingGroup (Fin 7)) →* ↥L := π₀
  have hπs : Function.Surjective π := hπs₀
  have hLs : L ≤ stabSub V := by
    intro g hg u
    refine ⟨fun hu => ?_, hinv g hg u⟩
    have h1 := hinv g⁻¹ (L.inv_mem hg) (g u) hu
    rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h1
  let act : ↥(alternatingGroup (Fin 7)) →* MulAut ↥V :=
    (resHom V).comp ((Subgroup.inclusion hLs).comp π)
  have hact : ∀ (g : ↥(alternatingGroup (Fin 7))) (v : ↥V),
      ((act g v : ↥V) : W) = ((π g : ↥L) : MulAut W) (v : W) := fun g v => rfl
  have hZfix : ∀ (g : ↥(alternatingGroup (Fin 7))), ∀ z ∈ (V ⊓ fixV L).subgroupOf V,
      act g z = z := by
    intro g z hz
    apply Subtype.ext
    rw [hact]
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).2 _ (π g).2
  have hker : β.ker = (V ⊓ fixV L).subgroupOf V := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have hQ : Nat.card (↥(FFModel.a7Four α).sec ⧸
      (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec) = 2 ^ 4 := by
    show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))).subgroupOf ⊤) = 2 ^ 4
    rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_fin]
  have hcard : Nat.card ↥V = 16 * Nat.card ↥((V ⊓ fixV L).subgroupOf V) := by
    have h1 := Subgroup.card_ker_mul_card_range β
    rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top, hker, hQ] at h1
    have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
    rw [h16] at h1
    omega
  have hgen : Subgroup.closure {x : ↥V | ∃ (g : ↥(alternatingGroup (Fin 7))) (v : ↥V),
      x = act g v * v⁻¹} = ⊤ := by
    set S : Subgroup ↥V := Subgroup.closure {x : ↥V | ∃ (g : ↥(alternatingGroup (Fin 7)))
      (v : ↥V), x = act g v * v⁻¹} with hS
    have hle : commSub V L ≤ S.map V.subtype := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      obtain ⟨g, hg⟩ := hπs ⟨x, hx⟩
      refine ⟨act g ⟨w, hw⟩ * (⟨w, hw⟩ : ↥V)⁻¹,
        Subgroup.subset_closure ⟨g, ⟨w, hw⟩, rfl⟩, ?_⟩
      show ((act g ⟨w, hw⟩ : ↥V) : W) * w⁻¹ = x w * w⁻¹
      rw [hact, hg]
    rw [eq_top_iff]
    intro u _
    have hu : (u : W) ∈ commSub V L := by rw [hcomm]; exact u.2
    obtain ⟨s, hs, hsu⟩ := hle hu
    have hsu' : s = u := Subtype.ext hsu
    rwa [hsu'] at hs
  have hZ := CFSG.QuasithinUnique.L246.C123.central_zero_abstract (V := ↥V)
    (fun v => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hW2 (v : W)))
    act (MonoidHom.id _) Function.surjective_id
    (fun q hq => by rw [show q = 1 from hq, map_one]) ((V ⊓ fixV L).subgroupOf V) hZfix hcard hgen
  rw [eq_bot_iff]
  intro w hw
  have h1 : (⟨w, hw.1⟩ : ↥V) ∈ (V ⊓ fixV L).subgroupOf V := Subgroup.mem_subgroupOf.2 hw
  rw [hZ, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)

end A7Cohomology

section D35Proof

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

private theorem d35_hypD31 (hD : D3Std M Mp T L V) : HypD31 M Mp T V :=
  ⟨⟨hD.hyp.exp, hD.hyp.qsqtk, hD.hyp.sylow, RonanD35.d3Std_Mp_le hD, hD.hyp.Mp_normal, hD.hyp.irr,
    hD.hyp.o2inv, hD.hyp.gen⟩, Or.inl ⟨L, hD.hyp.comp, hD.hyp.quasi, hD.hyp.Mp_eq⟩⟩

private theorem d35_inv (hD : D3Std M Mp T L V) (hMp : Mp = L) : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V := by
  subst hMp
  exact fun g hg v hv => hD.hyp.irr.2.1 ⟨g, hg⟩ v hv

private theorem d35_one (hD : D3Std M Mp T L V) (hMp : Mp = L) :
    Mp = L ∧ ∀ t ∈ T, ∀ x ∈ L, t * x * t⁻¹ ∈ L := by
  refine ⟨hMp, fun t ht x hx => ?_⟩
  have hn := hD.hyp.Mp_normal (hD.hyp.sylow.1 ht)
  rw [hMp] at hn
  exact (Subgroup.mem_normalizer_iff.mp hn x).mp hx

private theorem d35_fstar (hD : D3Std M Mp T L V) (hMp : Mp = L) :
    fstarSub (autSub (Mp ⊔ T) V) = autSub L V := by
  rw [(as_D_3_4 W M Mp T V (d35_hypD31 hD)).2.2.2.2.1.2.1, hMp]

private theorem d35_quasi (hD : D3Std M Mp T L V) (hMp : Mp = L) :
    CFSG.IsQuasisimple ↥(autSub L V) :=
  lred3_isQuasisimple_autSub (le_stabSub_of_forall_memQ2 (d35_inv hD hMp)) hD.hyp.quasi
    (lred3_exists_ne hD.hyp hMp)

private theorem d35_ff (hD : D3Std M Mp T L V) (hMp : Mp = L)
    (h5 : (∃ n, BinaryNaturalSL L V (V ⊓ fixV L) 3 n) ∨ (∃ n, BinaryNaturalSp4 L V (V ⊓ fixV L) n) ∨
      AlternatingNatural L V (V ⊓ fixV L) 6 ∨ BinaryNaturalSL L V (V ⊓ fixV L) 4 1 ∨
      BinaryNaturalSL L V (V ⊓ fixV L) 5 1 ∨ A7Four L V ⊥) :
    IsFFModule (autSub (Mp ⊔ T) V) := by
  obtain ⟨A, hA, hA1, hAe, hcard⟩ := RonanD35.isFFModule_of_d35List
    (fun w => by rw [← sq]; exact hD.hyp.exp w) (le_stabSub_of_forall_memQ2 (d35_inv hD hMp)) h5
  exact ⟨A, hA.trans (autSub_mono ((le_of_eq hMp.symm).trans le_sup_left) V), hA1, hAe, hcard⟩

private theorem d35_five (hD : D3Std M Mp T L V) (hMp : Mp = L)
    (h : D35Five L V) :
    (∃ n, BinaryNaturalSL L V (V ⊓ fixV L) 3 n) ∨ (∃ n, BinaryNaturalSp4 L V (V ⊓ fixV L) n) ∨
      AlternatingNatural L V (V ⊓ fixV L) 6 ∨ BinaryNaturalSL L V (V ⊓ fixV L) 4 1 ∨
      BinaryNaturalSL L V (V ⊓ fixV L) 5 1 ∨ A7Four L V ⊥ := by
  have hcomm : commSub V L = V := by
    subst hMp
    rw [← commOf_eq_commSub]
    exact hD.hyp.irr.2.2.1
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    have hz := a7Four_fixV_eq_bot hD.hyp.exp (d35_inv hD hMp) hcomm h
    rwa [hz] at h

end D35Proof

section D35


theorem as_D_3_5
    : D_3_5 := by
  intro W _ _ M Mp T L V hD hlt hcent
  obtain ⟨hMp, hex, hall, hfive⟩ := CFSG.Quasithin.H13.d35_proved W M Mp T L V hD hlt hcent
  have h5 := d35_five hD hMp hfive
  refine ⟨d35_one hD hMp, ⟨d35_ff hD hMp h5, d35_fstar hD hMp, d35_quasi hD hMp⟩, ?_, ⟨hex, hall⟩, h5⟩
  intro hC A hA hQ
  obtain ⟨t, ht, htV⟩ := hex
  obtain ⟨hTs, hsum⟩ := hall t ht htV
  exact RonanD35.d35_three hD hMp ht htV hTs hsum hC A hA hQ

end D35

section

theorem as_D_3_10
    : D_3_10 := by
  intro W _ _ M Mp T L V hD hMp hq
  have hW2 : ∀ w : W, w ^ 2 = 1 := hD.hyp.exp
  have hinv : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V := by
    subst hMp
    exact fun g hg v hv => hD.hyp.irr.2.1 ⟨g, hg⟩ v hv
  have hcomm : commSub V L = V := by
    subst hMp
    rw [← commOf_eq_commSub]
    exact hD.hyp.irr.2.2.1
  rcases CFSG.Quasithin.H13.d310_holds W M Mp T L V hD hMp hq with hT | ⟨hlist, hex, hall⟩
  · exact Or.inl ⟨hT, (orbSup_eq_of_stab hT).symm⟩
  · refine Or.inr ⟨?_, hex, ?_⟩
    · rcases hlist with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
        have hz := a7Four_fixV_eq_bot hW2 hinv hcomm h
        rwa [hz] at h
    · intro t ht htn
      obtain ⟨h1, h2⟩ := hall t ht htn
      exact ⟨by rwa [top_inf_eq], h2⟩

end

@[expose] def D_3_20 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → Mp = L → V ⊓ fixV L ≠ ⊥ → L ≤ ffJ M →
      M ≤ stabSub V ∧ V = orbSup T V ∧ orbSup T V = ⊤

theorem commV_eq_top_of_gen {W : Type} [CommGroup W] {M L : Subgroup (MulAut W)} {V : Subgroup W}
    (hn : ∀ m ∈ M, ∀ k ∈ L, m * k * m⁻¹ ∈ L) (hcomm : commSub V L = V)
    (hgen : (⨆ m ∈ M, V.map m.toMonoidHom) = ⊤) : commV L = ⊤ := by
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun m hm => ?_
  have h1 : V.map m.toMonoidHom = (commSub V L).map m.toMonoidHom := by rw [hcomm]
  rw [h1, commSub, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨_, ⟨x, hx, w, hw, rfl⟩, rfl⟩
  refine Subgroup.subset_closure ⟨m * x * m⁻¹, hn m hm x hx, m w, ?_⟩
  simp [MulAut.mul_apply]

section


private theorem d320_aux
    {W : Type} [CommGroup W] [Finite W] {M Mp T : Subgroup (MulAut W)}
    {V : Subgroup W} (hD : D3Std M Mp T Mp V) (hC : V ⊓ fixV Mp ≠ ⊥) (hLJ : Mp ≤ ffJ M) :
    M ≤ stabSub V ∧ V = orbSup T V ∧ orbSup T V = ⊤ := by
  have hD' := hD.hyp
  have hW2 : ∀ w : W, w ^ 2 = 1 := hD'.exp
  have hn : ∀ x ∈ M, ∀ k ∈ Mp, x * k * x⁻¹ ∈ Mp := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.mp (hD'.Mp_normal hx) k).mp hk
  have hVinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V := fun x hx v hv => hD'.irr.2.1 ⟨x, hx⟩ v hv
  have hcommV : commSub V Mp = V := by
    rw [← commOf_eq_commSub]
    exact hD'.irr.2.2.1
  have hcomm : commV Mp = ⊤ := commV_eq_top_of_gen hn hcommV hD'.gen
  have hq : CFSG.IsQuasisimple ↥Mp := hD'.quasi
  have hO2 : pCoreOf 2 M = ⊥ := D31.pCoreOf_eq_bot hD'
  have hJM : ffJ M ≤ M := B6.ffJ_le M
  have hJn : ∀ x ∈ ffJ M, ∀ k ∈ Mp, x * k * x⁻¹ ∈ Mp := fun x hx k hk => hn x (hJM hx) k hk
  have hMpne : Mp ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot Mp).mp (CFSG.LocalCores.isQuasisimple_nontrivial hq)
  have hJne : ffJ M ≠ ⊥ := by
    intro h
    rw [h] at hLJ
    exact hMpne (le_bot_iff.mp hLJ)
  have hJq : IsQuotientOfSQTKTC ↥(ffJ M) := n6_isQuotientOfSQTK_of_le hJM hD'.qsqtk
  have hQJ : pCoreOf 2 (ffJ M) = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 (ffJ M) M hJM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hJM).2 (B6.le_normalizer_ffJ M))
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hb53 : B53Hyp (ffJ M) := ⟨hQJ, (InternalSec.ffJ_ffJ M).symm, n6_b53_clause hJq⟩
  have hcases := asB56_holds W hW2 (ffJ M) hJne hb53
  have hF : quasithinGenFitting (ffJ M) = Mp :=
    InternalSec.quasithinGenFitting_eq_of_b56Cases_of_commV hLJ hJn hq hcomm hcases
  have hqF : CFSG.IsQuasisimple ↥(quasithinGenFitting (ffJ M)) := by
    rw [hF]
    exact hq
  have hLG : quasithinGenFitting (ffJ M) ≤ ffJ M := quasithinGenFitting_le _
  have hq' := FFC.isQuotientOfSQTKTauCeti_of_b53 hb53
  have hSQ := FFC.sqtk_of_le asA21SQTKSection hq' hLG hqF
  have hB51 : B51Hyp (ffJ M) (quasithinGenFitting (ffJ M)) :=
    ⟨by rw [sup_eq_left.2 (FFC.centerOf_le_genFitting (ffJ M))], hqF, hSQ, hLG, hb53.1, hb53.2.1⟩
  have hconc := B5.asB51_holds W hW2 (ffJ M) (quasithinGenFitting (ffJ M)) hB51
  rw [hF] at hconc
  have hP2 : B51Part2 Mp := hconc.2.1
  have hfixne : fixV Mp ⊓ commV Mp ≠ ⊥ := by
    rw [hcomm, inf_top_eq]
    intro h
    apply hC
    rw [h, inf_bot_eq]
  have hnd : ¬ IsIntDirect (commV Mp) (fixV Mp) ⊤ := hP2.1.mpr (Or.inl hfixne)
  have hirr : commV Mp ∈ IrrPlus Mp (⊤ : Subgroup W) := (hP2.2 hnd).1
  rw [hcomm, mem_irrPlus_top_iff] at hirr
  obtain ⟨-, -, -, hirr⟩ := hirr
  have hVtop : V = ⊤ := by
    rcases hirr (V ⊔ fixV Mp) (isInv_sup hVinv (isInv_fixV Mp))
        (by rw [top_inf_eq]; exact le_sup_right) le_top with h | h
    · exfalso
      have hVf : V ≤ fixV Mp := by
        have h1 : V ≤ V ⊔ fixV Mp := le_sup_left
        rw [h, top_inf_eq] at h1
        exact h1
      have hbot : commSub V Mp = ⊥ := commSub_eq_bot_iff.mpr hVf
      rw [hcommV] at hbot
      apply hC
      rw [hbot, bot_inf_eq]
    · have h1 : commSub (V ⊔ fixV Mp) Mp = commSub V Mp := commSub_sup_fixV le_rfl
      rw [h, ← commV_eq_commSub, hcomm, hcommV] at h1
      exact h1.symm
  rw [hVtop]
  exact ⟨fun g _ u => ⟨fun _ => trivial, fun _ => trivial⟩,
    (top_le_iff.mp (le_orbSup T ⊤)).symm, top_le_iff.mp (le_orbSup T ⊤)⟩

theorem as_D_3_20
    : D_3_20 := by
  intro W _ _ M Mp T L V hD hMp hC hLJ
  subst hMp
  exact d320_aux hD hC hLJ

end

@[expose] def D_3_21 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      Mp = L ⊔ conjAutSub t L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
        orbSup T V = ⊤ ∨
        (IsPSL 3 2 1 ↥L ∧ IsIntDirect (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
          commV L = fixV (conjAutSub t L) ∧
          DirectSumOfCopies L (commV L) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 ∧
          (∀ A ∈ QhatStar M, A ≤ stabSub (commV L)) ∧
          (Nat.card ↥(twoResidual (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 5 ∨
            (IsElemAbelian 5 (twoResidual (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) ∧
              Nat.card ↥(twoResidual (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 25))) ∨
        ((∃ n : ℕ, IsPSL 2 2 n ↥L) ∧
          IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
          commV L ≤ fixV (conjAutSub t L) ∧
          (∃ n : ℕ, IsPSL 2 2 n ↥L ∧
            ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
              DirectSumOfCopies L (commV L) (commV L ⊓ fixV Mp) (FFModel.nat (StatedSL 2 K)) 2) ∧
          M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ ∧
          ∃ I ∈ IrrPlus L (commV L), M ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub I)

section D321


theorem as_D_3_21
    : D_3_21 :=
  CFSG.Quasithin.RonanD321.d321c_holds

end D321

end CFSG.ASVolI
