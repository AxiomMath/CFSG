module

public import CFSG.Quasithin.Recognition.Stroth.Str83TwoArc
public import CFSG.Quasithin.Recognition.Stroth.Str83CartanTools
public import CFSG.GroupTheory.CyclicSubgroup.NormalizerCommutator
public import CFSG.GroupTheory.SubgroupSSupCommutative
public import CFSG.GH74.Uniqueness.Section4Lemma45

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

private theorem exists_reflection_of_vertex
    {L L' S B P D D' Kg : Subgroup G} {n i : ℕ}
    (hPdef : P = L ⊔ B)
    (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hBsyl : B ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G))
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hBt : BenderType (oTwoQuot ↥L) n i 1)
    (hD : RonanF13.HallTwoPrime D (borelOf L S))
    (hBD : borelOf L S = (S ⊓ L) ⊔ D)
    (hDcyc : IsCyclic ↥D)
    (hD'cyc : IsCyclic ↥D')
    (hcomm : ∀ x ∈ D, ∀ y ∈ D', x * y = y * x)
    (hHall : RonanF13.HallTwoPrime (D ⊔ D') B)
    (hcommLift : ∀ d ∈ D', ∃ δ ∈ D, ∀ l ∈ L,
      (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L)
    (hpcLQ : pCoreOf 2 L ≤ pCoreOf 2 P)
    (hKgP : Kg ≤ P) (hKgB : Kg ≤ B)
    (hPKg : P ≤ Subgroup.normalizer (Kg : Set G))
    (hKL : Kg ⊓ L = pCoreOf 2 L)
    (hQleK : pCoreOf 2 P ≤ Kg)
    (hQn : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set G))
    (hQsyl : IsSylowTwoOf (pCoreOf 2 P) Kg)
    (hKcent : ∀ t ∈ Kg, ∀ l ∈ L, l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L)
    (hmemK : ∀ x ∈ B, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) → x ∈ Kg) :
    ∃ x ∈ L ⊔ B, x ∉ B ∧
      (D ⊔ D').map (MulAut.conj x).toMonoidHom = D ⊔ D' ∧
      (∀ d ∈ D, x * d * x⁻¹ = d⁻¹) ∧
      (∀ h ∈ D ⊔ D', (∀ l ∈ L, h * l * h⁻¹ * l⁻¹ ∈ pCoreOf 2 L) →
        x * h * x⁻¹ = h) := by
  classical
  set Q : Subgroup G := pCoreOf 2 P with hQdef
  set H : Subgroup G := D ⊔ D' with hHdef
  have hLleP : L ≤ P := by rw [hPdef]; exact le_sup_left
  have hBleP : B ≤ P := by rw [hPdef]; exact le_sup_right
  have hHleB : H ≤ B := hHall.1
  have hHleP : H ≤ P := hHleB.trans hBleP
  have hHodd : Odd (Nat.card ↥H) := hHall.2.1
  have hDleH : D ≤ H := le_sup_left
  have hD'leH : D' ≤ H := le_sup_right
  have hDleB : D ≤ B := hDleH.trans hHleB
  have hD'leB : D' ≤ B := hD'leH.trans hHleB
  have hDleL : D ≤ L := hD.1.trans (F1.borelOf_le L S)
  have hHab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
    have hS : ∀ A ∈ ({D, D'} : Set (Subgroup G)), ∀ B ∈ ({D, D'} : Set (Subgroup G)),
        ⁅A, B⁆ = ⊥ := by
      intro A hA B hB
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
      rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
      · exact Subgroup.commutator_self_eq_bot_iff.mpr (IsCyclic.isMulCommutative)
      · refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (fun x hx => ?_)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hcomm x hx y hy).symm
      · rw [Subgroup.commutator_comm]
        refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (fun x hx => ?_)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hcomm x hx y hy).symm
      · exact Subgroup.commutator_self_eq_bot_iff.mpr (IsCyclic.isMulCommutative)
    haveI : IsMulCommutative ↥(D ⊔ D') := by
      have h := CFSG.GroupTheory.isMulCommutative_sSup hS
      rw [sSup_pair] at h
      exact h
    intro x hx y hy
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥(D ⊔ D'))).comm
      ⟨x, hx⟩ ⟨y, hy⟩)
  set N : Subgroup G := H ⊓ Kg with hNdef
  have hNleH : N ≤ H := inf_le_left
  have hNleK : N ≤ Kg := inf_le_right
  have hBKg : B ≤ Subgroup.normalizer (Kg : Set G) := hBleP.trans hPKg
  have hHallN : RonanF13.HallTwoPrime N Kg :=
    RonanF13.HallTwoPrime.inf hKgB hBKg hHall
  have hNodd : Odd (Nat.card ↥N) := hHallN.2.1
  have hDN : D ⊓ N = ⊥ := by
    have hle : D ⊓ N ≤ pCoreOf 2 L := by
      calc D ⊓ N ≤ L ⊓ Kg := inf_le_inf hDleL hNleK
        _ = pCoreOf 2 L := by rw [inf_comm]; exact hKL
    have hpc : pCoreOf 2 L ⊓ N = ⊥ :=
      RonanF13.inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hNodd
    exact le_bot_iff.mp ((le_inf hle inf_le_right).trans (le_of_eq hpc))
  have hNcyc : IsCyclic ↥N := by
    haveI : IsCyclic ↥D' := hD'cyc
    exact (CFSG.Semidihedral.StationaryConfinement.cyclic_of_inf_eq_bot_of_commute
      (W := D') (A₀ := D) (A' := N)
      (fun w hw a ha => (hcomm a ha w hw).symm)
      (by rw [sup_comm]; exact hNleH)
      (by rw [inf_comm]; exact hDN)).1
  haveI : IsCyclic ↥N := hNcyc
  have hD'leDN : D' ≤ D ⊔ N := by
    intro d hd
    obtain ⟨δ, hδD, hδcomm⟩ := hcommLift d hd
    have hzB : d * δ⁻¹ ∈ B := B.mul_mem (hD'leB hd) (B.inv_mem (hDleB hδD))
    have hzK : d * δ⁻¹ ∈ Kg := hmemK _ hzB hδcomm
    have hzH : d * δ⁻¹ ∈ H := H.mul_mem (hD'leH hd) (H.inv_mem (hDleH hδD))
    have hzN : d * δ⁻¹ ∈ N := ⟨hzH, hzK⟩
    have hdeq : d = (d * δ⁻¹) * δ := by group
    rw [hdeq]
    exact (D ⊔ N).mul_mem (Subgroup.mem_sup_right hzN) (Subgroup.mem_sup_left hδD)
  have hH_eq : H = D ⊔ N := by
    apply le_antisymm
    · calc H = D ⊔ D' := rfl
        _ ≤ D ⊔ (D ⊔ N) := sup_le le_sup_left (hD'leDN.trans le_sup_right)
        _ = D ⊔ N := by rw [← sup_assoc, sup_idem]
    · exact sup_le hDleH hNleH
  have hHcentN : H ≤ Subgroup.centralizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hHab x hx y (hNleH hy)).symm
  let Lbar := oTwoQuot ↥L
  let π : ↥L →* Lbar := QuotientGroup.mk' (pCore 2 ↥L)
  obtain ⟨hTpg, hTodd, hmapB⟩ := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hsyl
  let T : Subgroup Lbar := ((S ⊓ L).subgroupOf L).map π
  let Qs : Sylow 2 Lbar := hTpg.toSylow hTodd
  have hQscoe : (Qs : Subgroup Lbar) = T := IsPGroup.toSylow_coe hTpg hTodd
  let Dbar : Subgroup Lbar := (D.subgroupOf L).map π
  have hDbarodd : Odd (Nat.card ↥Dbar) := by
    have hle : Nat.card ↥Dbar ∣ Nat.card ↥D := by
      have h1 : Nat.card ↥(D.subgroupOf L) = Nat.card ↥D :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleL).toEquiv
      rw [show Dbar = (D.subgroupOf L).map π from rfl, ← h1]
      exact Subgroup.card_map_dvd _ π
    exact Odd.of_dvd_nat hD.2.1 hle
  have hDbarsup : (Qs : Subgroup Lbar) ⊔ Dbar = borel (Qs : Subgroup Lbar) := by
    have hmap_sup : ((S ⊓ L).subgroupOf L).map π ⊔ Dbar =
        (((S ⊓ L).subgroupOf L) ⊔ (D.subgroupOf L)).map π := by
      rw [Subgroup.map_sup]
    rw [hQscoe, hmap_sup,
      ← Subgroup.subgroupOf_sup (B := L) (inf_le_right : S ⊓ L ≤ L) hDleL, ← hBD]
    exact hmapB
  have hDbarle : Dbar ≤ borel (Qs : Subgroup Lbar) := by
    rw [← hDbarsup]
    exact le_sup_right
  obtain ⟨t, ht2, htQ, hcart⟩ :=
    exists_involution_cartan_eq hBt Qs hDbarle hDbarodd hDbarsup
  obtain ⟨t₀, hc₀⟩ := hBt.exists_benderCore Qs
  have hc : BenderCore (2 ^ n) i 1 (Qs : Subgroup Lbar) t := hc₀.of_involution ht2 htQ
  have hcartComm : cartan (Qs : Subgroup Lbar) t =
      ⁅cartan (Qs : Subgroup Lbar) t, Subgroup.zpowers t⁆ := hc.cartan_eq_commutator rfl
  have htinv : t⁻¹ = t := CFSG.GH74.Uniqueness.Bender.inv_eq_of_mul_self ht2
  have hPL : P ≤ Subgroup.normalizer (L : Set G) := by
    rw [hPdef]
    exact sup_le Subgroup.le_normalizer hBL
  let ρ0 : ↥(Subgroup.normalizer (L : Set G)) →* MulAut Lbar := oTwoQuotConj L
  let ρP : ↥P →* MulAut Lbar := ρ0.comp (Subgroup.inclusion hPL)
  have hρK : ∀ z (hz : z ∈ Kg), ρP ⟨z, hKgP hz⟩ = 1 := by
    intro z hz
    apply (oTwoQuotConj_eq_one_iff L ⟨z, hPL (hKgP hz)⟩).mpr
    intro l hl
    have h1 : l * z * l⁻¹ * z⁻¹ ∈ pCoreOf 2 L := hKcent z hz l hl
    have h2 : l⁻¹ * (l * z * l⁻¹ * z⁻¹) * l ∈ pCoreOf 2 L := by
      have h := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (L.inv_mem hl)) _).mp h1
      simpa using h
    simpa [mul_assoc] using h2
  have hρL : ∀ x : ↥L, ρP ⟨(x : G), hLleP x.2⟩ = MulAut.conj (π x) := by
    intro x
    exact oTwoQuotConj_eq_conj_mk x (Subgroup.le_normalizer x.2)
  have hInn_le : (MulAut.conj : Lbar →* MulAut Lbar).range ≤ ρP.range := by
    rintro σ ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L) z
    exact ⟨⟨(x : G), hLleP x.2⟩, hρL x⟩
  let C : Subgroup G := P ⊓ Subgroup.centralizer (N : Set G)
  let M0 : Subgroup G := P ⊓ Subgroup.normalizer (N : Set G)
  let ρM0 : ↥M0 →* MulAut Lbar := ρP.comp (Subgroup.inclusion (inf_le_left : M0 ≤ P))
  have hρP_eq : ρP.range = ρM0.range := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      obtain ⟨m, hm, hmg⟩ :=
        exists_mem_normalizer_of_frattini hKgP hPKg hQleK hQn hQsyl hHallN g g.2
      have hzK : m⁻¹ * (g : G) ∈ Kg := hQleK hmg
      have h1 : ρP g = ρP ⟨m, hm.1⟩ := by
        have hg_eq : g = ⟨m, hm.1⟩ * ⟨m⁻¹ * (g : G), hKgP hzK⟩ :=
          Subtype.ext (by simp)
        rw [hg_eq, map_mul, hρK _ hzK, mul_one]
      exact ⟨⟨m, hm⟩, h1.symm⟩
    · rintro _ ⟨m, rfl⟩
      exact ⟨⟨m, (inf_le_left : M0 ≤ P) m.2⟩, rfl⟩
  have hM0N : M0 ≤ Subgroup.normalizer (N : Set G) := inf_le_right
  have hM0C : ⁅M0, M0⁆ ≤ C :=
    le_inf ((Subgroup.commutator_le_self M0).trans (inf_le_left : M0 ≤ P))
      (CFSG.GroupTheory.CyclicSubgroup.commutator_le_centralizer N M0 M0 hM0N hM0N)
  have hBender : CFSG.BenderSuzuki.IsBenderGroup Lbar :=
    isBenderGroup_iff_exists_benderType.mpr ⟨n, i, 1, hBt⟩
  haveI : Group.IsPerfect Lbar := Group.isPerfect_def.mpr
    (CFSG.GH74.Uniqueness.commutator_eq_top_of_isBenderGroup hBender)
  haveI : Group.IsPerfect (MulAut.conj : Lbar →* MulAut Lbar).range :=
    Group.IsPerfect.range (f := (MulAut.conj : Lbar →* MulAut Lbar))
  have hInn_perf : (MulAut.conj : Lbar →* MulAut Lbar).range =
      ⁅(MulAut.conj : Lbar →* MulAut Lbar).range,
        (MulAut.conj : Lbar →* MulAut Lbar).range⁆ :=
    (Subgroup.commutator_eq_self
      (H := (MulAut.conj : Lbar →* MulAut Lbar).range)).symm
  let ρC : ↥C →* MulAut Lbar := ρP.comp (Subgroup.inclusion (inf_le_left : C ≤ P))
  have hcommM0 : ⁅ρM0.range, ρM0.range⁆ ≤ ρC.range := by
    rw [Subgroup.commutator_le]
    intro σ hσ τ hτ
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hσ
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hτ
    change ρM0 a * ρM0 b * (ρM0 a)⁻¹ * (ρM0 b)⁻¹ ∈ ρC.range
    have hab : ((a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹) ∈ ⁅M0, M0⁆ := by
      simpa only [commutatorElement_def] using
        Subgroup.commutator_mem_commutator a.2 b.2
    have habC : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ C :=
      hM0C hab
    let aP : ↥P := ⟨(a : G), (inf_le_left : M0 ≤ P) a.2⟩
    let bP : ↥P := ⟨(b : G), (inf_le_left : M0 ≤ P) b.2⟩
    have hmain : ρP (aP * bP * aP⁻¹ * bP⁻¹) =
        ρP aP * ρP bP * (ρP aP)⁻¹ * (ρP bP)⁻¹ := by
      simp only [map_mul, map_inv]
    refine ⟨⟨(a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹, habC⟩, ?_⟩
    change ρP (aP * bP * aP⁻¹ * bP⁻¹) =
      ρP aP * ρP bP * (ρP aP)⁻¹ * (ρP bP)⁻¹
    exact hmain
  have hInn_le_ρC : (MulAut.conj : Lbar →* MulAut Lbar).range ≤ ρC.range :=
    hInn_perf.le.trans ((Subgroup.commutator_mono (hInn_le.trans hρP_eq.le)
      (hInn_le.trans hρP_eq.le)).trans hcommM0)
  have htInn : MulAut.conj t ∈ (MulAut.conj : Lbar →* MulAut Lbar).range :=
    MonoidHom.mem_range.mpr ⟨t, rfl⟩
  obtain ⟨y, hyeq⟩ := MonoidHom.mem_range.mp (hInn_le_ρC htInn)
  have hyC : (y : G) ∈ C := y.2
  have hyP : (y : G) ∈ P := (inf_le_left : C ≤ P) hyC
  have hycen : (y : G) ∈ Subgroup.centralizer (N : Set G) :=
    (inf_le_right : C ≤ Subgroup.centralizer (N : Set G)) hyC
  have hyN : (y : G) ∈ Subgroup.normalizer (N : Set G) :=
    Subgroup.centralizer_le_normalizer (N : Set G) hycen
  have hyL : (y : G) ∈ Subgroup.normalizer (L : Set G) := hPL hyP
  have hyQ : (y : G) ∈ Subgroup.normalizer (Q : Set G) := hQn hyP
  have hyρ : oTwoQuotConj L ⟨(y : G), hPL hyP⟩ = MulAut.conj t := hyeq
  have hstep5 : ∀ g (hgC : g ∈ C), oTwoQuotConj L
      ⟨g, hPL ((inf_le_left : C ≤ P) hgC)⟩ = MulAut.conj t → conjSub g H ≤ H ⊔ Q := by
    intro g hgC hgρ
    have hgP : g ∈ P := (inf_le_left : C ≤ P) hgC
    have hgL : g ∈ Subgroup.normalizer (L : Set G) := hPL hgP
    have hgcen : g ∈ Subgroup.centralizer (N : Set G) :=
      (inf_le_right : C ≤ Subgroup.centralizer (N : Set G)) hgC
    have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := hQn hgP
    have hgD : ∀ d ∈ D, g * d * g⁻¹ ∈ H ⊔ Q := by
      intro d hd
      have hdL : d ∈ L := hDleL hd
      have hgdL : g * d * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgL d).mp hdL
      have hπd : π ⟨d, hdL⟩ ∈ cartan (Qs : Subgroup Lbar) t := by
        rw [hcart]
        exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hd)
      have ht_inv : t * π ⟨d, hdL⟩ * t = (π ⟨d, hdL⟩)⁻¹ := by
        have hx : π ⟨d, hdL⟩ ∈ ⁅cartan (Qs : Subgroup Lbar) t, Subgroup.zpowers t⁆ := by
          rw [← hcartComm]; exact hπd
        exact (hc.mem_commutator_cartan_iff).mp hx |>.2
      have hπgd : π ⟨g * d * g⁻¹, hgdL⟩ = (π ⟨d, hdL⟩)⁻¹ := by
        have hconj := oTwoQuotConj_mk L ⟨g, hgL⟩ ⟨d, hdL⟩
        calc π ⟨g * d * g⁻¹, hgdL⟩
            = oTwoQuotConj L ⟨g, hgL⟩ (π ⟨d, hdL⟩) := hconj.symm
          _ = MulAut.conj t (π ⟨d, hdL⟩) := by rw [hgρ]
          _ = (π ⟨d, hdL⟩)⁻¹ := by rw [MulAut.conj_apply, htinv, ht_inv]
      have hπprod : π ⟨(g * d * g⁻¹) * d, L.mul_mem hgdL hdL⟩ = 1 := by
        have hsplit : (⟨(g * d * g⁻¹) * d, L.mul_mem hgdL hdL⟩ : ↥L) =
            ⟨g * d * g⁻¹, hgdL⟩ * ⟨d, hdL⟩ := Subtype.ext rfl
        rw [hsplit, map_mul, hπgd, inv_mul_cancel]
      have hprodL : (g * d * g⁻¹) * d ∈ pCoreOf 2 L := by
        have hmem : (⟨(g * d * g⁻¹) * d, L.mul_mem hgdL hdL⟩ : ↥L) ∈ pCore 2 ↥L := by
          rw [← QuotientGroup.eq_one_iff]
          exact hπprod
        exact (CFSG.Quasithin.F1.mem_pCore_iff_coe _).mp hmem
      have hprodQ : (g * d * g⁻¹) * d ∈ Q := hpcLQ hprodL
      have hdeq : g * d * g⁻¹ = ((g * d * g⁻¹) * d) * d⁻¹ := by group
      rw [hdeq]
      exact (H ⊔ Q).mul_mem (Subgroup.mem_sup_right hprodQ)
        (Subgroup.mem_sup_left (H.inv_mem (hDleH hd)))
    have hgNfix : ∀ n ∈ N, g * n * g⁻¹ = n := by
      intro n hn
      have h := (Subgroup.mem_centralizer_iff.mp hgcen) n hn
      calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [← h]
        _ = n := by group
    have hgNfixN : conjSub g N = N :=
      CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
        (Subgroup.centralizer_le_normalizer (N : Set G) hgcen)
    calc conjSub g H = conjSub g (D ⊔ N) := by rw [hH_eq]
      _ = conjSub g D ⊔ conjSub g N := conjSub_sup g D N
      _ = conjSub g D ⊔ N := by rw [hgNfixN]
      _ ≤ H ⊔ Q := by
        refine sup_le (fun z hz => ?_) (hNleH.trans (le_sup_left : H ≤ H ⊔ Q))
        obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hz
        exact hgD d hd
  have hyStep : conjSub (y : G) H ≤ H ⊔ Q := hstep5 (y : G) hyC hyρ
  have hyinvρ : oTwoQuotConj L ⟨(y : G)⁻¹, hPL ((inf_le_left : C ≤ P) (C.inv_mem hyC))⟩ =
      MulAut.conj t := by
    have h1 : ρC (y⁻¹) = (ρC y)⁻¹ := map_inv ρC y
    calc oTwoQuotConj L ⟨(y : G)⁻¹, hPL ((inf_le_left : C ≤ P) (C.inv_mem hyC))⟩
        = ρC (y⁻¹) := rfl
      _ = (ρC y)⁻¹ := h1
      _ = (MulAut.conj t)⁻¹ := by rw [hyeq]
      _ = MulAut.conj t⁻¹ := (map_inv _ t).symm
      _ = MulAut.conj t := by rw [htinv]
  have hyHQ : conjSub (y : G) (H ⊔ Q) = H ⊔ Q := by
    have hrev : conjSub (y : G)⁻¹ (H ⊔ Q) ≤ H ⊔ Q := by
      rw [conjSub_sup, CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
        ((Subgroup.normalizer (Q : Set G)).inv_mem hyQ)]
      exact sup_le (hstep5 (y : G)⁻¹ (C.inv_mem hyC) hyinvρ)
        (le_sup_right : Q ≤ H ⊔ Q)
    apply le_antisymm
    · rw [conjSub_sup, CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer hyQ]
      exact sup_le hyStep (le_sup_right : Q ≤ H ⊔ Q)
    · calc H ⊔ Q = conjSub (y : G) (conjSub (y : G)⁻¹ (H ⊔ Q)) :=
          (conjSub_inv_conjSub (y : G) (H ⊔ Q)).symm
        _ ≤ conjSub (y : G) (H ⊔ Q) := conjSub_mono _ hrev
  let M : Subgroup G := (H ⊔ Q) ⊓ C
  have hHleM : H ≤ M := le_inf le_sup_left ((le_inf hHleP hHcentN) : H ≤ C)
  have hMC : M ≤ C := inf_le_right
  have hMP : M ≤ P := hMC.trans (inf_le_left : C ≤ P)
  have hyM : conjSub (y : G) M = M := by
    rw [show M = (H ⊔ Q) ⊓ C from rfl, conjSub_inf, hyHQ,
      CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hyC)]
  have hyNM : (y : G) ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hyM
  have hMsupH : M = H ⊔ (Q ⊓ M) := by
    apply le_antisymm
    · intro m hm
      have hmHQ : m ∈ H ⊔ Q := (inf_le_left : M ≤ H ⊔ Q) hm
      have hmC : m ∈ C := hMC hm
      obtain ⟨h, hh, q, hq, hmq⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer
          ((hHleB.trans hBleP).trans hQn)).mp hmHQ
      have hqC : q ∈ C := by
        have hqeq : q = h⁻¹ * m := by rw [hmq]; group
        rw [hqeq]
        exact C.mul_mem (C.inv_mem ((le_inf hHleP hHcentN) hh)) hmC
      have hqM : q ∈ M := ⟨Subgroup.mem_sup_right hq, hqC⟩
      rw [hmq]
      exact Subgroup.mul_mem_sup hh (Subgroup.mem_inf.mpr ⟨hq, hqM⟩)
    · exact sup_le hHleM inf_le_right
  have hHD : H ⊓ (Q ⊓ M) = ⊥ := by
    have hQH : Q ⊓ H = ⊥ :=
      RonanF13.inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) hHodd
    rw [← inf_assoc, inf_comm H Q, hQH, bot_inf_eq]
  have hKcleM : conjSub (y : G) H ≤ M := by
    calc conjSub (y : G) H ≤ conjSub (y : G) M := conjSub_mono _ hHleM
      _ = M := hyM
  have hyQM : conjSub (y : G) (Q ⊓ M) = Q ⊓ M := by
    rw [conjSub_inf, CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer hyQ,
      CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer hyNM]
  have hQMsup : M = (Q ⊓ M) ⊔ conjSub (y : G) H := by
    have h1 := congrArg (conjSub (y : G)) hMsupH
    rw [conjSub_sup, hyQM, hyM] at h1
    rw [sup_comm]
    exact h1
  have hQMbot : (Q ⊓ M) ⊓ conjSub (y : G) H = ⊥ := by
    have h := congrArg (conjSub (y : G)) hHD
    rw [conjSub_inf, hyQM, conjSub_bot] at h
    rw [inf_comm]
    exact h
  have hMnormQM : M ≤ Subgroup.normalizer ((Q ⊓ M : Subgroup G) : Set G) :=
    (le_inf (fun m hm => hQn (hMP hm)) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  let N' : Subgroup ↥M := (Q ⊓ M).subgroupOf M
  let H' : Subgroup ↥M := H.subgroupOf M
  let K' : Subgroup ↥M := (conjSub (y : G) H).subgroupOf M
  have hN'norm : N'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hMnormQM
  have hcompH : N'.IsComplement' H' := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext z
      constructor
      · rintro ⟨hzN, hzH⟩
        apply Subtype.ext
        have hz : (z : G) ∈ H ⊓ (Q ⊓ M) := ⟨hzH, hzN⟩
        rw [hHD] at hz
        exact Subgroup.mem_bot.mp hz
      · intro hz
        rw [Subgroup.mem_bot] at hz
        subst hz
        exact ⟨N'.one_mem, H'.one_mem⟩
    · have hsup : N' ⊔ H' = ⊤ := by
        rw [← Subgroup.subgroupOf_sup (inf_le_right : Q ⊓ M ≤ M) hHleM]
        have h : (Q ⊓ M) ⊔ H = M := by rw [sup_comm]; exact hMsupH.symm
        rw [h, Subgroup.subgroupOf_self]
      rw [← Subgroup.normal_mul N' H', hsup]
      rfl
  have hcompK : N'.IsComplement' K' := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext z
      constructor
      · rintro ⟨hzN, hzK⟩
        apply Subtype.ext
        have hz : (z : G) ∈ (Q ⊓ M) ⊓ conjSub (y : G) H := ⟨hzN, hzK⟩
        rw [hQMbot] at hz
        exact Subgroup.mem_bot.mp hz
      · intro hz
        rw [Subgroup.mem_bot] at hz
        subst hz
        exact ⟨N'.one_mem, K'.one_mem⟩
    · have hsup : N' ⊔ K' = ⊤ := by
        rw [← Subgroup.subgroupOf_sup (inf_le_right : Q ⊓ M ≤ M) hKcleM]
        have h : (Q ⊓ M) ⊔ conjSub (y : G) H = M := hQMsup.symm
        rw [h, Subgroup.subgroupOf_self]
      rw [← Subgroup.normal_mul N' K', hsup]
      rfl
  have hcop : Nat.Coprime (Nat.card ↥N') N'.index := by
    rw [hcompH.symm.index_eq_card]
    have hcardH' : Nat.card ↥H' = Nat.card ↥H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleM).toEquiv
    rw [hcardH']
    have hN'2 : IsPGroup 2 ↥N' :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).to_le (inf_le_left : Q ⊓ M ≤ Q)).of_equiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q ⊓ M ≤ M)).symm
    obtain ⟨m, hm⟩ := hN'2.exists_card_eq
    rw [hm]
    exact (Nat.coprime_two_left.mpr hHodd).pow_left m
  obtain ⟨n, hn⟩ := CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
    N' H' K' hN'norm hcompH hcompK hcop
  have hKcEq : conjSub (y : G) H =
      H.map (MulAut.conj (((n : ↥M) : G))).toMonoidHom := by
    have h := congrArg (fun X : Subgroup ↥M => X.map M.subtype) hn
    rw [Subgroup.map_subgroupOf_eq_of_le hKcleM, Subgroup.map_map] at h
    have hcomp : M.subtype.comp (MulAut.conj (n : ↥M)).toMonoidHom =
        (MulAut.conj (((n : ↥M) : G))).toMonoidHom.comp M.subtype := by
      ext z
      rfl
    rw [hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hHleM] at h
    exact h
  have hnQM : ((n : ↥M) : G) ∈ Q ⊓ M := Subgroup.mem_subgroupOf.mp n.2
  have hnP : ((n : ↥M) : G) ∈ P := hMP hnQM.2
  have hnC : ((n : ↥M) : G) ∈ C := hMC hnQM.2
  have hxPmem : (((n : ↥M) : G))⁻¹ * (y : G) ∈ P :=
    P.mul_mem (P.inv_mem hnP) hyP
  let xP : ↥P := ⟨(((n : ↥M) : G))⁻¹ * (y : G), hxPmem⟩
  let x : G := (xP : G)
  have hxdef : x = (((n : ↥M) : G))⁻¹ * (y : G) := rfl
  have hxH : conjSub x H = H := by
    have hKc' : conjSub (y : G) H = conjSub (((n : ↥M) : G)) H := by
      rw [hKcEq]
      rfl
    rw [hxdef, conjSub_mul, hKc', conjSub_conjSub_inv]
  have hxρ : ρP xP = MulAut.conj t := by
    have hxP_eq : xP = (⟨((n : ↥M) : G), hnP⟩ : ↥P)⁻¹ * ⟨(y : G), hyP⟩ :=
      Subtype.ext (by simp [xP])
    have hnρ : ρP ⟨((n : ↥M) : G), hnP⟩ = 1 := hρK _ (hQleK hnQM.1)
    have hyρP : ρP ⟨(y : G), hyP⟩ = MulAut.conj t := hyeq
    rw [hxP_eq, map_mul, map_inv, hnρ, hyρP, inv_one, one_mul]
  have hxB : x ∉ B := by
    intro hxB
    have hxS : x ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := hBsyl hxB
    have hxT : ∀ z ∈ (Qs : Subgroup Lbar), ρP xP z ∈ (Qs : Subgroup Lbar) := by
      intro z hz
      rw [hQscoe] at hz ⊢
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hz
      have hsS : (s : G) ∈ S ⊓ L := Subgroup.mem_subgroupOf.mp hs
      have hxs : (x : G) * (s : G) * (x : G)⁻¹ ∈ S ⊓ L :=
        (Subgroup.mem_normalizer_iff.mp hxS (s : G)).mp hsS
      have hval : ρP xP (π s) = π ⟨(x : G) * (s : G) * (x : G)⁻¹, hxs.2⟩ :=
        oTwoQuotConj_mk L ⟨(x : G), hPL xP.2⟩ s
      rw [hval]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxs)
    have htN : t ∈ CFSG.GH74.Uniqueness.Bender.borel (Qs : Subgroup Lbar) := by
      rw [CFSG.GH74.Uniqueness.Bender.borel, Subgroup.mem_normalizer_iff, htinv]
      intro z
      constructor
      · intro hz
        have h := hxT z hz
        rw [hxρ, MulAut.conj_apply, htinv] at h
        exact h
      · intro hz
        have h := hxT (t * z * t) hz
        rw [hxρ, MulAut.conj_apply, htinv] at h
        rwa [show t * (t * z * t) * t = z from by
          calc t * (t * z * t) * t = (t * t) * z * (t * t) := by group
            _ = z := by rw [ht2, one_mul, mul_one]] at h
    exact htQ htN
  have hxinv : ∀ d ∈ D, x * d * x⁻¹ = d⁻¹ := by
    intro d hd
    have hdL : d ∈ L := hDleL hd
    have hxdL : x * d * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hPL xP.2) d).mp hdL
    have hxdH : x * d * x⁻¹ ∈ H := by
      have hmem : x * d * x⁻¹ ∈ conjSub x H :=
        Subgroup.mem_map.mpr ⟨d, hDleH hd, rfl⟩
      rwa [hxH] at hmem
    have hπxd : π ⟨x * d * x⁻¹, hxdL⟩ = (π ⟨d, hdL⟩)⁻¹ := by
      have hπd : π ⟨d, hdL⟩ ∈ cartan (Qs : Subgroup Lbar) t := by
        rw [hcart]
        exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hd)
      have ht_inv : t * π ⟨d, hdL⟩ * t = (π ⟨d, hdL⟩)⁻¹ := by
        have hx : π ⟨d, hdL⟩ ∈ ⁅cartan (Qs : Subgroup Lbar) t, Subgroup.zpowers t⁆ := by
          rw [← hcartComm]; exact hπd
        exact (hc.mem_commutator_cartan_iff).mp hx |>.2
      have hconj := oTwoQuotConj_mk L ⟨(x : G), hPL xP.2⟩ ⟨d, hdL⟩
      calc π ⟨x * d * x⁻¹, hxdL⟩
          = oTwoQuotConj L ⟨(x : G), hPL xP.2⟩ (π ⟨d, hdL⟩) := hconj.symm
        _ = MulAut.conj t (π ⟨d, hdL⟩) := by
          rw [show oTwoQuotConj L ⟨(x : G), hPL xP.2⟩ = ρP xP from rfl, hxρ]
        _ = (π ⟨d, hdL⟩)⁻¹ := by rw [MulAut.conj_apply, htinv, ht_inv]
    have hprodL : (x * d * x⁻¹) * d ∈ pCoreOf 2 L := by
      have hπprod : π ⟨(x * d * x⁻¹) * d, L.mul_mem hxdL hdL⟩ = 1 := by
        have hsplit : (⟨(x * d * x⁻¹) * d, L.mul_mem hxdL hdL⟩ : ↥L) =
            ⟨x * d * x⁻¹, hxdL⟩ * ⟨d, hdL⟩ := Subtype.ext rfl
        rw [hsplit, map_mul, hπxd, inv_mul_cancel]
      have hmem : (⟨(x * d * x⁻¹) * d, L.mul_mem hxdL hdL⟩ : ↥L) ∈ pCore 2 ↥L := by
        rw [← QuotientGroup.eq_one_iff]
        exact hπprod
      exact (CFSG.Quasithin.F1.mem_pCore_iff_coe _).mp hmem
    have hprodH : (x * d * x⁻¹) * d ∈ H := H.mul_mem hxdH (hDleH hd)
    have hbot : (x * d * x⁻¹) * d ∈ pCoreOf 2 L ⊓ H := ⟨hprodL, hprodH⟩
    rw [RonanF13.inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hHodd] at hbot
    have hone : (x * d * x⁻¹) * d = 1 := Subgroup.mem_bot.mp hbot
    calc x * d * x⁻¹ = ((x * d * x⁻¹) * d) * d⁻¹ := by group
      _ = d⁻¹ := by rw [hone, one_mul]
  have hxcentN : ∀ z ∈ N, x * z * x⁻¹ = z := by
    intro z hz
    have hncent : ∀ w ∈ N, ((n : ↥M) : G) * w * (((n : ↥M) : G))⁻¹ = w := by
      intro w hw
      have h := (Subgroup.mem_centralizer_iff.mp
        ((inf_le_right : C ≤ Subgroup.centralizer (N : Set G)) hnC)) w hw
      calc ((n : ↥M) : G) * w * (((n : ↥M) : G))⁻¹ = w * ((n : ↥M) : G) * (((n : ↥M) : G))⁻¹ := by
            rw [← h]
        _ = w := by group
    have hycent : (y : G) * z * (y : G)⁻¹ = z := by
      have h := (Subgroup.mem_centralizer_iff.mp hycen) z hz
      calc (y : G) * z * (y : G)⁻¹ = z * (y : G) * (y : G)⁻¹ := by rw [← h]
        _ = z := by group
    have hncent' : ∀ w ∈ N, (((n : ↥M) : G))⁻¹ * w * ((n : ↥M) : G) = w := by
      intro w hw
      have h := hncent w hw
      calc (((n : ↥M) : G))⁻¹ * w * ((n : ↥M) : G)
          = (((n : ↥M) : G))⁻¹ * ((((n : ↥M) : G)) * w * (((n : ↥M) : G))⁻¹) *
              (((n : ↥M) : G)) := by rw [h]
        _ = w := by group
    calc x * z * x⁻¹ = (((n : ↥M) : G))⁻¹ * ((y : G) * z * (y : G)⁻¹) * ((n : ↥M) : G) := by
          rw [hxdef]; group
      _ = (((n : ↥M) : G))⁻¹ * z * ((n : ↥M) : G) := by rw [hycent]
      _ = z := hncent' z hz
  refine ⟨x, ?_, hxB, ?_, hxinv, ?_⟩
  · rw [← hPdef]
    exact xP.2
  · show (D ⊔ D').map (MulAut.conj x).toMonoidHom = D ⊔ D'
    exact hxH
  · intro h hh hcommh
    have hhB : h ∈ B := hHleB hh
    have hhK : h ∈ Kg := hmemK h hhB hcommh
    exact hxcentN h ⟨hh, hhK⟩

theorem f112_exists_reflection_left
    {L1 L2 S : Subgroup G} {a f : ℕ} (hF : F112HypW L1 L2 S)
    (hN : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hf : 2 ≤ f) (hL2 : IsL2Quot f (oTwoQuot ↥L2))
    {D1 D2 : Subgroup G} (hD1 : RonanF13.HallTwoPrime D1 (borelOf L1 S))
    (hD2 : RonanF13.HallTwoPrime D2 (borelOf L2 S))
    (hB1D : borelOf L1 S = (S ⊓ L1) ⊔ D1) (hB2D : borelOf L2 S = (S ⊓ L2) ⊔ D2)
    (hcomm : ∀ x ∈ D1, ∀ y ∈ D2, x * y = y * x)
    (hHall : RonanF13.HallTwoPrime (D1 ⊔ D2) (bigB L1 L2 S)) :
    ∃ x ∈ L1 ⊔ bigB L1 L2 S, x ∉ bigB L1 L2 S ∧
      (D1 ⊔ D2).map (MulAut.conj x).toMonoidHom = D1 ⊔ D2 ∧
      (∀ d ∈ D1, x * d * x⁻¹ = d⁻¹) ∧
      (∀ h ∈ D1 ⊔ D2, (∀ l ∈ L1, h * l * h⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) → x * h * x⁻¹ = h) := by
  classical
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hBt1 : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (Classical.choice hSz |>.trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hBt2 : BenderType (oTwoQuot ↥L2) f 1 1 :=
    BenderType.linear f hf (Classical.choice hL2)
  have hL1s : IsSimpleGroup (oTwoQuot ↥L1) := hBt1.isSimple
  set P1 : Subgroup G := L1 ⊔ bigB L1 L2 S with hP1def
  set Q1 : Subgroup G := pCoreOf 2 P1 with hQ1def
  set K1 : Subgroup G := (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype with hK1def
  have hK1leP1 : K1 ≤ P1 := Subgroup.map_subtype_le _
  have hK1gB : K1 ≤ bigB L1 L2 S := by
    have hK1le : f112K1 L1 L2 S ≤ (P1 ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf P1 :=
      Subgroup.normalCore_le _
    have hmap := Subgroup.map_mono (f := P1.subtype) hK1le
    rw [Subgroup.map_subgroupOf_eq_of_le
      (inf_le_left : P1 ⊓ (L2 ⊔ bigB L1 L2 S) ≤ P1)] at hmap
    have hinf : P1 ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S := f112_parabolic_inf_eq_bigB hF
    rwa [hinf] at hmap
  have hK1n : P1 ≤ Subgroup.normalizer (K1 : Set G) :=
    CFSG.ABGLocalTools.le_normalizer_map_subtype P1 (f112K1 L1 L2 S)
  have hE1 : S = (S ⊓ L1) ⊔ Q1 :=
    eq_sup_pCoreOf_of_bender_left hF.1 hN (Or.inl ⟨a, ha, hSz⟩)
  have hK1S : K1 ⊓ S = Q1 := inf_K1_map_sup_eq_pCoreOf hF hL1s hE1
  have hQ1leK1 : Q1 ≤ K1 := pCoreOf_le_K1_map hF
  have hQ1n : P1 ≤ Subgroup.normalizer (Q1 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P1
  have hQ1syl : IsSylowTwoOf Q1 K1 := by
    have h := CFSG.Quasithin.B6.isSylowTwoOf_inf_normal
      (f112_isSylowTwoOf_P1 hF) hK1leP1 hK1n
    rwa [inf_comm, hK1S] at h
  have hK1L : K1 ⊓ L1 = pCoreOf 2 L1 := by
    rw [inf_comm]
    exact f112_inf_map_K1_eq_pCoreOf hF hL1s
  have hD1cyc : IsCyclic ↥D1 :=
    (card_isCyclic_of_hallTwoPrime hF.1.h1.sylow hD1 hB1D hBt1).2
  have hD2cyc : IsCyclic ↥D2 :=
    (card_isCyclic_of_hallTwoPrime hF.1.h2.sylow hD2 hB2D hBt2).2
  have hD2leB : D2 ≤ bigB L1 L2 S := (le_sup_right : D2 ≤ D1 ⊔ D2).trans hHall.1
  have hcommLift : ∀ d ∈ D2, ∃ δ ∈ D1, ∀ l ∈ L1,
      (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1 := fun d hd =>
    exists_commutator_lift hF.1 hR hD1 hB1D hD2leB hcomm hBt1
      (fun Q t ht htQ σ hσQ hσD =>
        BenderType.aut_eq_conj_cartan_suzuki hBt1 Q ht htQ σ hσQ hσD) hd
  have hmemK : ∀ x ∈ bigB L1 L2 S,
      (∀ l ∈ L1, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) → x ∈ K1 := by
    intro x hx hc
    have hmap : x ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype :=
      Subgroup.mem_map_of_mem (L1 ⊔ bigB L1 L2 S).subtype
        (f112_mem_K1_of_commutator_mem hF.1 hx hc)
    rwa [← hK1def] at hmap
  exact exists_reflection_of_vertex (L := L1) (L' := L2) (S := S) (B := bigB L1 L2 S)
    (P := P1) (D := D1) (D' := D2) (Kg := K1) (n := 2 * a + 1) (i := 2)
    hP1def hF.1.h1.sylow (F1.bigB_le_normalizer_sylow hR).1
    (F1.bigB_le_normalizer_left hR).1 hBt1 hD1 hB1D hD1cyc hD2cyc hcomm hHall hcommLift
    (Hyp111.pCoreOf_le_pCoreOf_vertex hF.1) hK1leP1 hK1gB hK1n hK1L hQ1leK1 hQ1n hQ1syl
    (f112_kernel_centralizes_of_isSimpleGroup hF hL1s) hmemK

theorem f112_exists_reflection_right
    {L1 L2 S : Subgroup G} {a f : ℕ} (hF : F112HypW L1 L2 S)
    (hN : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hf : 2 ≤ f) (hL2 : IsL2Quot f (oTwoQuot ↥L2))
    {D1 D2 : Subgroup G} (hD1 : RonanF13.HallTwoPrime D1 (borelOf L1 S))
    (hD2 : RonanF13.HallTwoPrime D2 (borelOf L2 S))
    (hB1D : borelOf L1 S = (S ⊓ L1) ⊔ D1) (hB2D : borelOf L2 S = (S ⊓ L2) ⊔ D2)
    (hcomm : ∀ x ∈ D1, ∀ y ∈ D2, x * y = y * x)
    (hHall : RonanF13.HallTwoPrime (D1 ⊔ D2) (bigB L1 L2 S)) :
    ∃ x ∈ L2 ⊔ bigB L1 L2 S, x ∉ bigB L1 L2 S ∧
      (D1 ⊔ D2).map (MulAut.conj x).toMonoidHom = D1 ⊔ D2 ∧
      (∀ d ∈ D2, x * d * x⁻¹ = d⁻¹) ∧
      (∀ h ∈ D1 ⊔ D2, (∀ l ∈ L2, h * l * h⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x * h * x⁻¹ = h) := by
  classical
  have hF' : F112HypW L2 L1 S := F112HypW.symm hF
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hR' : Hyp111R L2 L1 S := Hyp111R.of_hyp111 rankOneListedFacts hF'.1
  have hBt2 : BenderType (oTwoQuot ↥L2) f 1 1 :=
    BenderType.linear f hf (Classical.choice hL2)
  have hL2s : IsSimpleGroup (oTwoQuot ↥L2) := hBt2.isSimple
  set P2 : Subgroup G := L2 ⊔ bigB L1 L2 S with hP2def
  set Q2 : Subgroup G := pCoreOf 2 P2 with hQ2def
  set K2 : Subgroup G := (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype with hK2def
  have hK2leP2 : K2 ≤ P2 := Subgroup.map_subtype_le _
  have hK2gB : K2 ≤ bigB L1 L2 S := by
    have hK2le : f112K2 L1 L2 S ≤ (P2 ⊓ (L1 ⊔ bigB L1 L2 S)).subgroupOf P2 :=
      Subgroup.normalCore_le _
    have hmap := Subgroup.map_mono (f := P2.subtype) hK2le
    rw [Subgroup.map_subgroupOf_eq_of_le
      (inf_le_left : P2 ⊓ (L1 ⊔ bigB L1 L2 S) ≤ P2)] at hmap
    have hinf : P2 ⊓ (L1 ⊔ bigB L1 L2 S) = bigB L1 L2 S := by
      rw [inf_comm]; exact f112_parabolic_inf_eq_bigB hF
    rwa [hinf] at hmap
  have hK2n : P2 ≤ Subgroup.normalizer (K2 : Set G) :=
    CFSG.ABGLocalTools.le_normalizer_map_subtype P2 (f112K2 L1 L2 S)
  have hE2 : S = (S ⊓ L2) ⊔ Q2 :=
    eq_sup_pCoreOf_of_bender_right hF.1 hN (Or.inr (Or.inr ⟨f, hf, hL2⟩))
  have hK2S : K2 ⊓ S = Q2 := inf_K2_map_sup_eq_pCoreOf hF hL2s hE2
  have hQ2leK2 : Q2 ≤ K2 := pCoreOf_le_K2_map hF
  have hQ2n : P2 ≤ Subgroup.normalizer (Q2 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P2
  have hQ2syl : IsSylowTwoOf Q2 K2 := by
    have h := CFSG.Quasithin.B6.isSylowTwoOf_inf_normal
      (f112_isSylowTwoOf_P2 hF) hK2leP2 hK2n
    rwa [inf_comm, hK2S] at h
  have hK2L : K2 ⊓ L2 = pCoreOf 2 L2 := by
    rw [inf_comm]
    exact f112_inf_map_K2_eq_pCoreOf hF hL2s
  have hD1cyc : IsCyclic ↥D1 :=
    (card_isCyclic_of_hallTwoPrime hF.1.h1.sylow hD1 hB1D
      (BenderType.suzuki a ha (Classical.choice hSz |>.trans
        (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))).2
  have hD2cyc : IsCyclic ↥D2 :=
    (card_isCyclic_of_hallTwoPrime hF.1.h2.sylow hD2 hB2D hBt2).2
  have hHall' : RonanF13.HallTwoPrime (D2 ⊔ D1) (bigB L1 L2 S) := by
    rw [sup_comm D2 D1]
    exact hHall
  have hcomm' : ∀ x ∈ D2, ∀ y ∈ D1, x * y = y * x :=
    fun x hx y hy => (hcomm y hy x hx).symm
  have hD1leB' : D1 ≤ bigB L2 L1 S := by
    rw [bigB_comm]
    exact (le_sup_left : D1 ≤ D1 ⊔ D2).trans hHall.1
  have hcommLift : ∀ d ∈ D1, ∃ δ ∈ D2, ∀ l ∈ L2,
      (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 := fun d hd =>
    exists_commutator_lift hF'.1 hR' hD2 hB2D hD1leB' hcomm' hBt2
      (fun Q t ht htQ σ hσQ hσD =>
        BenderType.aut_eq_conj_cartan_linear hBt2 Q ht htQ σ hσQ hσD) hd
  have hpcLQ : pCoreOf 2 L2 ≤ pCoreOf 2 P2 := by
    have h := Hyp111.pCoreOf_le_pCoreOf_vertex hF'.1
    rwa [bigB_comm L1 L2 S] at h
  have hmemK : ∀ x ∈ bigB L1 L2 S,
      (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x ∈ K2 := by
    intro x hx hc
    have hmap : x ∈ (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype :=
      Subgroup.mem_map_of_mem (L2 ⊔ bigB L1 L2 S).subtype
        (f112_mem_K2_of_commutator_mem hF.1 hx hc)
    rwa [← hK2def] at hmap
  simpa only [sup_comm D2 D1] using
    (exists_reflection_of_vertex (L := L2) (L' := L1) (S := S) (B := bigB L1 L2 S)
      (P := P2) (D := D2) (D' := D1) (Kg := K2) (n := f) (i := 1)
      hP2def hF.1.h2.sylow (F1.bigB_le_normalizer_sylow hR).2
      (F1.bigB_le_normalizer_left hR).2 hBt2 hD2 hB2D hD2cyc hD1cyc hcomm' hHall' hcommLift
      hpcLQ hK2leP2 hK2gB hK2n hK2L hQ2leK2 hQ2n hQ2syl
      (f112_kernel_centralizes_of_isSimpleGroup_right hF hL2s) hmemK)

end CFSG.Quasithin.Stroth

end
