module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.SimpleStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSQTK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedCore
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.Quasithin.SteinbergBSDihedralPair
public import CFSG.Quasithin.SteinbergBSCubicPair

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.Quasithin.B6

theorem map_eq_one_of_odd_card {G G' : Type*} [Group G] [Group G'] {N : Subgroup G'}
    (hN : Odd (Nat.card N)) (f : G →* G') {x : G} (hx : f x ∈ N) {n : ℕ} (hxn : x ^ 2 ^ n = 1) :
    f x = 1 := by
  have h1 : orderOf (⟨f x, hx⟩ : N) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [← map_pow, hxn]))
  have h2 : orderOf (⟨f x, hx⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) (Nat.card N) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hN)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)

theorem qrc_original_single_core_faithful_section_preselector
    {H : Type} [Group H] [Finite H]
    (hns : ¬ Group.IsSolvable H) (hsqtk : CFSG.SectionRank.IsSQTKCat H) (T : Sylow 2 H)
    (hTn : ¬ (T : Subgroup H).Normal) {M : Subgroup H} (hTM : (T : Subgroup H) ≤ M)
    (hMH : M < ⊤) (hmax : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y < ⊤ → Y ≤ M)
    {V : Subgroup H} [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) (hVM : V ≤ inSubgroup (pCore 2) M)
    (hVQ : 4 ≤ (V ⊓ pCore 2 H).relIndex V)
    (hK : IsSimpleGroup ↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))) :
    pCore 2 H ≤ kerIn M ⊤ ∧ Odd ((pCore 2 H).relIndex (kerIn M ⊤)) ∧
    oddResidualPreimage H ⊔ T = ⊤ ∧
    (((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))).Normal ∧
      (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)) ≠ ⊥ ∧
      ∀ N : Subgroup (H ⧸ kerIn M ⊤), N.Normal → N ≠ ⊥ →
        (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)) ≤ N) ∧
    (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)) ⊔
      (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) = ⊤ ∧
    (∃ S : Sylow 2 (H ⧸ kerIn M ⊤),
      (S : Subgroup (H ⧸ kerIn M ⊤)) = (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤))) ∧
    centralizer ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)) :
      Set (H ⧸ kerIn M ⊤)) = ⊥ ∧
    (∃ ι : H ⧸ kerIn M ⊤ →*
        MulAut ↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))),
      Function.Injective ι ∧ ∀ a k, ((ι a k : H ⧸ kerIn M ⊤)) = a * k * a⁻¹) ∧
    ((T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ≤ M.map (QuotientGroup.mk' (kerIn M ⊤)) ∧
      M.map (QuotientGroup.mk' (kerIn M ⊤)) < ⊤ ∧
      ∀ Y : Subgroup (H ⧸ kerIn M ⊤), (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ≤ Y →
        Y < ⊤ → Y ≤ M.map (QuotientGroup.mk' (kerIn M ⊤))) ∧
    kerIn (M.map (QuotientGroup.mk' (kerIn M ⊤))) ⊤ = ⊥ ∧
    (IsElementaryAbelian 2 ↥(V.map (QuotientGroup.mk' (kerIn M ⊤))) ∧
      Nat.card ↥(V.map (QuotientGroup.mk' (kerIn M ⊤))) = (V ⊓ pCore 2 H).relIndex V ∧
      4 ≤ Nat.card ↥(V.map (QuotientGroup.mk' (kerIn M ⊤))) ∧
      V.map (QuotientGroup.mk' (kerIn M ⊤)) ≤ (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ∧
      (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ≤
        normalizer (V.map (QuotientGroup.mk' (kerIn M ⊤)) : Set (H ⧸ kerIn M ⊤)) ∧
      V.map (QuotientGroup.mk' (kerIn M ⊤)) ≤
        inSubgroup (pCore 2) (M.map (QuotientGroup.mk' (kerIn M ⊤)))) ∧
    CFSG.SectionRank.IsSQTKCat (H ⧸ kerIn M ⊤) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (T : Subgroup H) ⊤ := ⟨le_top, T.isPGroup', by
    show ¬ 2 ∣ (T : Subgroup H).relIndex ⊤
    rw [relIndex_top_right]
    exact T.not_dvd_index⟩
  obtain ⟨⟨hRJ, hJK⟩, ⟨-, hodd, -⟩, hHKT, ⟨hKn₀, -⟩, hcomp, hsimp⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hTsyl hTn hTM hMH hmax
  set Q := pCore 2 H with hQdef
  set J := kerIn M ⊤ with hJdef
  set π := QuotientGroup.mk' J with hπdef
  set K₀ := oddResidualPreimage H with hK₀def
  set K := K₀.map π with hKdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  have hπker : π.ker = J := QuotientGroup.ker_mk' J
  have hQR : Q = CFSG.Open.pCore 2 H := CFSG.pCore_eq_open H 2
  have hQJ : Q ≤ J := hQR ▸ hRJ
  have hDQ : Q.relIndex J = Nat.card (J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 H))) := by
    have h1 := card_inf_ker_mul_card_map (QuotientGroup.mk' (CFSG.Open.pCore 2 H)) J
    rw [QuotientGroup.ker_mk', inf_eq_right.2 hRJ] at h1
    have h2 := relIndex_mul_card (CFSG.Open.pCore 2 H) J
    rw [inf_eq_left.2 hRJ] at h2
    rw [hQR]
    have hpos : 0 < Nat.card (CFSG.Open.pCore 2 H) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans (h1.symm.trans (mul_comm _ _)))
  have hKn : K.Normal := hKn₀.map π hπs
  have hK1 : K ≠ ⊥ := by
    obtain ⟨x, hxK, hxJ⟩ := IsConcreteLE.exists_of_lt hJK
    intro hbot
    apply hxJ
    have h1 : π x ∈ K := mem_map_of_mem π hxK
    rw [hbot, mem_bot] at h1
    rw [← hπker]
    exact h1
  have hmin : ∀ N : Subgroup (H ⧸ J), N.Normal → N ≠ ⊥ → K ≤ N := by
    intro N hN hN1
    have hN' : (N.comap π).Normal := hN.comap π
    have hRN : CFSG.Open.pCore 2 H ≤ N.comap π := fun x hx => by
      have h : x ∈ π.ker := by
        rw [hπker]
        exact hRJ hx
      rw [mem_comap, MonoidHom.mem_ker.1 h]
      exact one_mem N
    have hNJ : ¬ N.comap π ≤ J := by
      intro hle
      apply hN1
      rw [← map_comap_eq_self_of_surjective hπs N, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_bot, ← MonoidHom.mem_ker, hπker]
      exact hle hx
    have h1 := hcomp _ hN' hRN hNJ
    rw [← map_comap_eq_self_of_surjective hπs N]
    exact map_mono h1
  have hKnab : ¬ IsMulCommutative ↥K := by
    obtain ⟨L, -, hLnc, hLK, -⟩ := hsimp hns
    intro hc
    apply hLnc
    exact ⟨⟨fun a b => Subtype.ext (show (a : H ⧸ J) * b = b * a from congrArg Subtype.val
      (mul_comm' (⟨a, hLK a.2⟩ : K) ⟨b, hLK b.2⟩))⟩⟩
  have hCK : centralizer (K : Set (H ⧸ J)) = ⊥ := by
    by_contra hne
    have hCn : (centralizer (K : Set (H ⧸ J))).Normal := ⟨fun c hc g k hk => by
      have hk' : g⁻¹ * k * g ∈ K := by
        have h1 := hKn.conj_mem k hk g⁻¹
        rwa [inv_inv] at h1
      have h1 := mem_centralizer_iff.1 hc _ hk'
      calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * k := by group⟩
    have hKC := hmin _ hCn hne
    exact hKnab ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.1 (hKC b.2) a a.2)⟩⟩
  have hKS : K ⊔ (T : Subgroup H).map π = ⊤ := by
    rw [hKdef, ← Subgroup.map_sup, hHKT, Subgroup.map_top_of_surjective π hπs]
  have hJM : J ≤ M := kerIn_le
  have hcomapB : (M.map π).comap π = M := by
    rw [comap_map_eq, hπker, sup_eq_left.2 hJM]
  have hBtop : M.map π < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hMH.ne ?_
    rw [← hcomapB, h, comap_top]
  have hBmax : ∀ Y : Subgroup (H ⧸ J), (T : Subgroup H).map π ≤ Y → Y < ⊤ → Y ≤ M.map π := by
    intro Y hTY hY
    have h1 : (T : Subgroup H) ≤ Y.comap π := map_le_iff_le_comap.1 hTY
    have h2 : Y.comap π < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => hY.ne ?_
      rw [← map_comap_eq_self_of_surjective hπs Y, h, map_top_of_surjective π hπs]
    rw [← map_comap_eq_self_of_surjective hπs Y]
    exact map_mono (hmax _ h1 h2)
  have hcore : kerIn (M.map π) ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h, rfl⟩ := hπs x
    rw [mem_bot, ← MonoidHom.mem_ker, hπker, hJdef, mem_kerIn]
    intro g _
    have h1 := (mem_kerIn.1 hx) (π g) (mem_top _)
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    have h2 : g * h * g⁻¹ ∈ (M.map π).comap π := h1
    rwa [hcomapB] at h2
  have hVDQ : V ⊓ J = V ⊓ Q := by
    refine le_antisymm (fun v hv => ?_) (inf_le_inf_left V hQJ)
    obtain ⟨hvV, hvJ⟩ := mem_inf.1 hv
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨v, hVT hvV⟩
    have hvn : v ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have h1 := map_eq_one_of_odd_card hodd (QuotientGroup.mk' (CFSG.Open.pCore 2 H))
      (mem_map_of_mem _ hvJ) hvn
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_inf.2 ⟨hvV, hQR ▸ h1⟩
  have hEcard : Nat.card ↥(V.map π) = (V ⊓ Q).relIndex V := by
    have h1 := card_inf_ker_mul_card_map π V
    rw [hπker, hVDQ] at h1
    have h2 := relIndex_mul_card (V ⊓ Q) V
    rw [inf_eq_left.2 inf_le_left] at h2
    have hpos : 0 < Nat.card ↥(V ⊓ Q) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos ((mul_comm _ _).trans (h1.trans h2.symm))
  have hMO : M ≤ normalizer (inSubgroup (pCore 2) M : Set H) :=
    le_normalizer.trans (normalizer_le_normalizer_map_characteristic M (pCore 2 M))
  have hEO : V.map π ≤ inSubgroup (pCore 2) (M.map π) := by
    refine (map_mono hVM).trans (le_inSubgroup_pCore (map_mono (map_subtype_le _)) ?_ ?_)
    · refine le_normalizer_of_forall_conj_mem ?_
      rintro _ ⟨m, hm, rfl⟩ _ ⟨o, ho, rfl⟩
      refine ⟨m * o * m⁻¹, (mem_normalizer_iff.mp (hMO hm) o).mp ho, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · exact ((pCore_isPGroup (p := 2) (G := M)).map M.subtype).map π
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hKnab ⟨⟨hcon⟩⟩
  have hlayer : CFSG.layer ↥K = ⊤ := by
    rw [CFSG.layer_eq_componentClassification]
    exact CFSG.ComponentClassification.SimpleStructure.layer_eq_top ↥K hnonab
  have h2K : IsPGroup 2 ((H ⧸ J) ⧸ K) := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have ha : a ∈ (T : Subgroup H).map π ⊔ K := by
      rw [sup_comm, hKS]
      exact mem_top a
    obtain ⟨s, hs, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ha
    obtain ⟨n, hn⟩ := (T.isPGroup'.map π) ⟨s, hs⟩
    have hsn : s ^ 2 ^ n = 1 := congrArg Subtype.val hn
    refine ⟨n, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).2 hk, mul_one, ← QuotientGroup.mk_pow,
      hsn, QuotientGroup.mk_one]
  have hsqtkA := (CFSG.QuasithinUnique.Setup.Layer.sqtk_two_power_index
    CFSG.SectionRank.oddKernelCentralization CFSG.SectionRank.catalogStepHyp hsqtk ⊤
    (π.comp (⊤ : Subgroup H).subtype) (fun y => by
      obtain ⟨h, rfl⟩ := hπs y
      exact ⟨⟨h, mem_top h⟩, rfl⟩) K hlayer h2K).1
  refine ⟨hQJ, ?_, hHKT, ⟨hKn, hK1, hmin⟩, hKS,
    ⟨T.mapSurjective hπs, Sylow.coe_mapSurjective hπs T⟩, hCK,
    ⟨MulAut.conjNormal, ?_, fun a k => MulAut.conjNormal_apply a k⟩,
    ⟨map_mono hTM, hBtop, hBmax⟩, hcore,
    ⟨IsElementaryAbelian.map π, hEcard, hEcard ▸ hVQ, map_mono hVT, ?_, hEO⟩, hsqtkA⟩
  · rw [hDQ]
    exact hodd
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hCK]
    intro a ha
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : H ⧸ J)) (MonoidHom.mem_ker.1 ha)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * a = a * k * a⁻¹ * a := by rw [h1]
      _ = a * k := by group
  · refine le_normalizer_of_forall_conj_mem ?_
    rintro _ ⟨t, ht, rfl⟩ _ ⟨v, hv, rfl⟩
    refine ⟨t * v * t⁻¹, (mem_normalizer_iff.mp (hTV ht) v).mp hv, ?_⟩
    rw [map_mul, map_mul, map_inv]

end CFSG.Quasithin.SteinbergBS
