module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.Quasithin.H13.KGFact1468Gen
public import CFSG.Quasithin.Background.A312SporHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Sporadic.Schreier.J4SLocalNodes
public import CFSG.Sporadic.Schreier.J4SOuter
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Timmesfeld.Orders.ClassicalLinear
import all CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.H13.L32AKG1468

public section

namespace CFSG.Quasithin.H13.KG1468

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem card_inf_centralizer_mul_ncard {G : Type*} [Group G] [Finite G] (K : Subgroup G) (y : G) :
    Nat.card ↥(K ⊓ Subgroup.centralizer ({y} : Set G)) *
      {m | ∃ k ∈ K, m = k * y * k⁻¹}.ncard = Nat.card K := by
  let _ : MulAction ↥K G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp K.subtype)
  have horb : MulAction.orbit ↥K y = {m | ∃ k ∈ K, m = k * y * k⁻¹} := by
    ext m
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hstab : MulAction.stabilizer ↥K y =
      (K ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨k.2, ?_⟩
      have h' : (k : G) * y * (k : G)⁻¹ = y := h
      calc (k : G) * y = (k : G) * y * (k : G)⁻¹ * k := by group
        _ = y * k := by rw [h']
    · rintro ⟨-, h⟩
      show (k : G) * y * (k : G)⁻¹ = y
      rw [h]
      group
  have h1 := MulAction.index_stabilizer ↥K y
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer ↥K y)
  rw [h1, horb, hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h2
  exact h2

theorem exists_map_sylow_eq {Γ : Type} [Group Γ] [Finite Γ] (S₀ : Subgroup Γ)
    (hS₀ : IsSylowTwoOf S₀ ⊤) {X : Type} [Group X] [Finite X] (e : X ≃* Γ) {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : ∃ ψ : X ≃* Γ, T.map ψ.toMonoidHom = S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := isSylowTwoOf_map e hT
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S₀ = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hST, Subgroup.map_map]
  rfl

theorem card_centralizer_mulEquiv {X Γ : Type} [Group X] [Group Γ] (ψ : X ≃* Γ) (x : X) :
    Nat.card (Subgroup.centralizer ({x} : Set X)) =
      Nat.card (Subgroup.centralizer ({ψ x} : Set Γ)) := by
  have h : (Subgroup.centralizer ({x} : Set X)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ x} : Set Γ) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg ψ h
      simpa using this
    · intro h
      apply ψ.injective
      simpa using h
  rw [← h, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]


theorem map_pCoreOf_le {X Γ : Type} [Group X] [Group Γ] [Finite X] [Finite Γ] (ψ : X ≃* Γ)
    (C : Subgroup X) : (pCoreOf 2 C).map ψ.toMonoidHom ≤ pCoreOf 2 (C.map ψ.toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (Open.pCore 2 ↥C).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 C)) ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C).map ψ.toMonoidHom)
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono (Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _))

theorem map_pCoreOf_eq {X Γ : Type} [Group X] [Group Γ] [Finite X] [Finite Γ] (ψ : X ≃* Γ)
    (C : Subgroup X) : (pCoreOf 2 C).map ψ.toMonoidHom = pCoreOf 2 (C.map ψ.toMonoidHom) := by
  refine le_antisymm (map_pCoreOf_le ψ C) ?_
  have h := map_pCoreOf_le ψ.symm (C.map ψ.toMonoidHom)
  have hC : (C.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = C := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id C
    ext y
    simp
  rw [hC] at h
  have h2 := Subgroup.map_mono (f := ψ.toMonoidHom) h
  rwa [Subgroup.map_map, show ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id Γ by
    ext y; simp, Subgroup.map_id] at h2

theorem exists_member_of_lattice {Γ : Type} [Group Γ] [Finite Γ] (S : Subgroup Γ)
    (hS : IsSylowTwoOf S ⊤) (J : ℕ) (Y : ℕ → Subgroup Γ)
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ J, Z = memberOrTop J Y j)
    {X : Type} [Group X] [Finite X] (e : X ≃* Γ) {T Z : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hTZ : T ≤ Z) :
    ∃ ψ : X ≃* Γ, ∃ j ≤ J, Z.map ψ.toMonoidHom = memberOrTop J Y j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := isSylowTwoOf_map e hT
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  let ψ : X ≃* Γ := e.trans (MulAut.conj g)
  have hψ : T.map ψ.toMonoidHom = S := by
    rw [hST, Subgroup.map_map]
    rfl
  have hSZ : S ≤ Z.map ψ.toMonoidHom := by
    rw [← hψ]
    exact Subgroup.map_mono hTZ
  obtain ⟨j, hj, hZ⟩ := hall _ hSZ
  exact ⟨ψ, j, hj, hZ⟩



theorem card_l34 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 2 2) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem not_bad_m24
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* Carrier .M24)) {x : X} (hx : IsTwoCentralInvolution ⊤ x) : ¬ Bad x := by
  obtain ⟨-, -, S, hS, -, hxc⟩ := hx
  have hSC : S ≤ Subgroup.centralizer ({x} : Set X) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hxc s hs)
  apply not_bad_of_card
  rcases M24.m24_overgroups hX hS hSC with h | ⟨m, hm, hcard, -, -⟩
  · obtain ⟨e⟩ := hX
    right; left
    rw [h, Subgroup.card_top, Nat.card_congr e.toEquiv,
      show Nat.card (Carrier .M24) = 244823040 from CFSG.Sporadic.Mathieu.card_M24]
    norm_num
  · rw [hcard]
    have key : ∀ m ∈ M24.m24Mems, ¬ 5 ∣ m.order ∨ 9 ∣ m.order ∨ 7 ∣ m.order ∨
        11 ∣ m.order := by decide
    exact key m hm

theorem not_bad_he
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* Carrier .He)) {x : X} (hx : IsTwoCentralInvolution ⊤ x) : ¬ Bad x := by
  obtain ⟨-, -, S, hS, -, hxc⟩ := hx
  have hSC : S ≤ Subgroup.centralizer ({x} : Set X) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hxc s hs)
  apply not_bad_of_card
  rcases He.he_overgroups hX hS hSC with h | ⟨m, hm, hcard, -, -⟩
  · obtain ⟨e⟩ := hX
    right; left
    rw [h, Subgroup.card_top, Nat.card_congr e.toEquiv,
      show Nat.card (Carrier .He) = 4030387200 from CFSG.Sporadic.He.card_He]
    norm_num
  · rw [hcard]
    have key : ∀ m ∈ He.heMems, ¬ 5 ∣ m.order ∨ 9 ∣ m.order ∨ 7 ∣ m.order ∨
        11 ∣ m.order := by decide
    exact key m hm

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4 in
theorem j4_centralizer_N :
    Subgroup.centralizer (N : Set J) = N := by
  have h := QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2
  have hle : Subgroup.centralizer (N : Set J) ≤ H := by
    rw [← normalizer_N]
    exact Subgroup.centralizer_le_normalizer _
  exact (inf_eq_left.mpr hle).symm.trans h

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4 in
theorem j4_nine_dvd
    {y : J} (hy : y ∈ N) (hy1 : y ≠ 1) :
    9 ∣ Nat.card (Subgroup.centralizer ({y} : Set J)) := by
  have hc := card_inf_centralizer_mul_ncard K y
  rw [card_K] at hc
  have hdvd : Nat.card ↥(K ⊓ Subgroup.centralizer ({y} : Set J)) ∣
      Nat.card (Subgroup.centralizer ({y} : Set J)) := Subgroup.card_dvd_of_le inf_le_right
  refine dvd_trans ?_ hdvd
  have hfacts := QT_unique_J4_local_normal_module_irreducible
  rcases hfacts.1 y hy with h | h | h
  · exact absurd h hy1
  · have hO : {m | ∃ k ∈ K, m = k * y * k⁻¹}.ncard = 1771 := by
      have : conjOrbit K y = conjOrbit K (η 1) := conjOrbit_eq_of_mem h
      rw [← hfacts.2.2.2.1]
      exact congrArg Set.ncard this
    rw [hO] at hc
    have : Nat.card ↥(K ⊓ Subgroup.centralizer ({y} : Set J)) = 138240 := by omega
    rw [this]
    norm_num
  · have hO : {m | ∃ k ∈ K, m = k * y * k⁻¹}.ncard = 276 := by
      have : conjOrbit K y = conjOrbit K (η 14) := conjOrbit_eq_of_mem h
      rw [← hfacts.2.2.2.2.1]
      exact congrArg Set.ncard this
    rw [hO] at hc
    have : Nat.card ↥(K ⊓ Subgroup.centralizer ({y} : Set J)) = 887040 := by omega
    rw [this]
    norm_num

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4 in
theorem not_bad_j4
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4)) {x : X}
    (hx : IsTwoCentralInvolution ⊤ x) : ¬ Bad x := by
  obtain ⟨e⟩ := hX
  obtain ⟨-, hx2, S, hS, hxS, hxc⟩ := hx
  have hS0 : IsSylowTwoOf (S0Sylow : Subgroup J) ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨S0Sylow.isPGroup', S0Sylow.not_dvd_index⟩
  obtain ⟨ψ, hψ⟩ := @exists_map_sylow_eq J (Subgroup.toGroup J) _ _ hS0 X _ _
    (e.trans (seedEquiv j4Facts.mat)) S hS
  apply not_bad_of_card
  right; left
  rw [@card_centralizer_mulEquiv X J _ (Subgroup.toGroup J) ψ x]
  have hyS : ψ x ∈ (S0Sylow : Subgroup J) := hψ ▸ ⟨x, hxS, rfl⟩
  have hyN : ψ x ∈ N := by
    rw [← j4_centralizer_N, Subgroup.mem_centralizer_iff]
    intro n hn
    have hnS : n ∈ S.map ψ.toMonoidHom := by
      rw [hψ, S0Sylow_coe]
      exact N_le_S0 hn
    obtain ⟨s, hs, rfl⟩ := hnS
    show ψ s * ψ x = ψ x * ψ s
    rw [← map_mul, ← map_mul, hxc s hs]
  have hy1 : ψ x ≠ 1 := by
    intro h
    apply (show x ≠ 1 from fun h1 => by rw [h1, orderOf_one] at hx2; omega)
    exact ψ.injective (h.trans (map_one ψ).symm)
  exact j4_nine_dvd hyN hy1


open CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.A312S
  CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.HS.Native (hsData) in
theorem not_bad_hs
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .HS)) {x : X}
    (hx : IsTwoCentralInvolution ⊤ x) : ¬ Bad x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hX
  obtain ⟨-, -, S, hS, -, hxc⟩ := hx
  set C := Subgroup.centralizer ({x} : Set X) with hCdef
  have hSC : S ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hxc s hs)
  have hX' : Nonempty (X ≃* J hsData) := ⟨e.trans (seedEquiv hs_facts.toBaseFacts)⟩
  obtain ⟨e'⟩ := hX'
  obtain ⟨ψ, j, hj, hZ⟩ :=
    exists_member_of_lattice hsCtx.S hs_S_sylow 5 hsCtx.Y hs_complete e' hS hSC
  have hcardC : Nat.card C = Nat.card (C.map ψ.toMonoidHom) :=
    (Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective).symm
  by_cases hj5 : j < 5
  · have hm : memberOrTop 5 hsCtx.Y j = hsCtx.Y j := by simp [memberOrTop, hj5]
    rw [hm] at hZ
    have hcj := hs_member_card j hj5
    interval_cases j
    · apply not_bad_of_card
      left
      rw [hcardC, hZ, hcj]
      decide
    · rintro ⟨-, A, hAR, hAab, -, h16⟩
      have hQmap : (pCoreOf 2 C).map ψ.toMonoidHom =
          Subgroup.closure {y | y ∈ hsZ4Elt :: hsEElts} := by
        rw [map_pCoreOf_eq, hZ, hs_O2Y1]
      obtain ⟨⟨Z, hZV, hZ4, hZc⟩, ⟨a, ha, b, hb, hab⟩⟩ := center_four_of_isZ4StarExtra2 hs_V1.1
      have hQ64 : Nat.card (pCoreOf 2 C) = 64 := by
        rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hQmap, hs_V1.2]
      let ZX : Subgroup X := Z.map ψ.symm.toMonoidHom
      have hmemQ : ∀ y, y ∈ pCoreOf 2 C ↔ ψ y ∈ Subgroup.closure {y | y ∈ hsZ4Elt :: hsEElts} := by
        intro y
        rw [← hQmap]
        constructor
        · intro hy
          exact ⟨y, hy, rfl⟩
        · rintro ⟨y', hy', hyy⟩
          rw [ψ.injective hyy] at hy'
          exact hy'
      have hZXQ : ZX ≤ pCoreOf 2 C := by
        rintro _ ⟨z, hz, rfl⟩
        rw [hmemQ]
        simpa using hZV hz
      have hZX4 : Nat.card ZX = 4 := by
        rw [Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) ψ.symm.injective, hZ4]
      have hZXc : ∀ z ∈ ZX, ∀ q ∈ pCoreOf 2 C, z * q = q * z := by
        rintro _ ⟨z, hz, rfl⟩ q hq
        apply ψ.injective
        rw [map_mul, map_mul]
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        exact hZc z hz (ψ q) ((hmemQ q).mp hq)
      have hna : ∃ a ∈ pCoreOf 2 C, ∃ b ∈ pCoreOf 2 C, a * b ≠ b * a := by
        refine ⟨ψ.symm a, (hmemQ _).mpr (by simpa using ha), ψ.symm b,
          (hmemQ _).mpr (by simpa using hb), fun h => hab ?_⟩
        have := congrArg ψ h
        simpa using this
      have hlt := relIndex_lt_of_center hQ64 hZXQ hZX4 hZXc hna (pCoreOf_oTwoUpper_le C) hAR hAab
      rw [hCdef] at hlt
      omega
    · apply not_bad_of_card
      right; right; left
      rw [hcardC, hZ, hcj]
      decide
    · apply not_bad_of_card
      left
      rw [hcardC, hZ, hcj]
      decide
    · apply not_bad_of_card
      left
      rw [hcardC, hZ, hcj]
      decide
  · have hm : memberOrTop 5 hsCtx.Y j = ⊤ := by simp [memberOrTop, hj5]
    rw [hm] at hZ
    apply not_bad_of_card
    right; left
    rw [hcardC, hZ, Subgroup.card_top, hs_card]
    decide


@[expose] def KG1468G24 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (x : X), ChevalleyExceptionalModel X .G2 2 2 →
    orderOf x = 2 → ¬ Bad x

theorem kg1468Ident_of
    (hG24 : KG1468G24) :
    KG1468Ident := by
  intro X _ _ x hx
  rcases hx with ⟨hL | hG, hx2⟩ | ⟨⟨s, hs, hsRu, hX⟩, hx⟩
  · exact not_bad_of_two_part (by rw [card_l34 hL]; norm_num) x
  · exact hG24 X x hG hx2
  · obtain ⟨e⟩ := hX
    have hc := Nat.card_congr e.toEquiv
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine not_bad_of_two_part ?_ x
      rw [hc, show Nat.card (Carrier .M11) = 7920 from CFSG.Sporadic.Mathieu.card_M11]
      norm_num
    · refine not_bad_of_two_part ?_ x
      rw [hc, show Nat.card (Carrier .M12) = 95040 from CFSG.Sporadic.Mathieu.card_M12]
      norm_num
    · refine not_bad_of_two_part ?_ x
      rw [hc, show Nat.card (Carrier .M22) = 443520 from CFSG.Sporadic.Mathieu.card_M22]
      norm_num
    · refine not_bad_of_two_part ?_ x
      rw [hc, show Nat.card (Carrier .M23) = 10200960 from CFSG.Sporadic.Schreier.m23_card]
      norm_num
    · exact not_bad_m24 ⟨e⟩ hx
    · refine not_bad_of_two_part ?_ x
      rw [hc, show Nat.card (Carrier .J2) = 604800 from CFSG.Sporadic.J2.card_J2]
      norm_num
    · exact not_bad_j4 ⟨e⟩ hx
    · exact not_bad_hs ⟨e⟩ hx
    · exact not_bad_he ⟨e⟩ hx
    · exact absurd rfl hsRu

end CFSG.Quasithin.H13.KG1468
