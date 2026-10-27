module

public import CFSG.Quasithin.Vol2.KGFact4413OneA
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftOne
public import CFSG.Quasithin.Vol2.KGFact4413K

public section

namespace CFSG.Quasithin.H13.KG4413

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem star_inf_eq {M H X Y : Subgroup Γ} (hX : kerIn M H ≤ X) :
    E2.star M H (X ⊓ Y) = E2.star M H X ⊓ E2.star M H Y := by
  have hker : (starPi M H).ker ≤ X.subgroupOf H := by
    intro x hx
    rw [MonoidHom.mem_ker, starPi_eq_one_iff] at hx
    exact Subgroup.mem_subgroupOf.mpr (hX hx)
  have h1 := Vol2.Ch11.SecB.map_inf_eq_of_ker_le (starPi M H) (Q := Y.subgroupOf H) hker
  rw [← Vol2.Ch11.SecB.inf_subgroupOf'] at h1
  exact h1

omit [Finite Γ] in
theorem cjSub_one (K : Subgroup Γ) : cjSub 1 K = K := by
  ext x
  rw [mem_cjSub]
  simp

theorem exists_conj_le_of_le_sup {Y : Type} [Group Y] [Finite Y] {N P X : Subgroup Y}
    (hN : IsPGroup 2 N) (hP : Odd (Nat.card P)) (hPN : P ≤ Subgroup.normalizer (N : Set Y))
    (hX : Odd (Nat.card X)) (hXle : X ≤ P ⊔ N) :
    ∃ n ∈ N, X.map (MulAut.conj n).toMonoidHom ≤ P := by
  have hNN : P ⊔ N ≤ Subgroup.normalizer (N : Set Y) := sup_le hPN Subgroup.le_normalizer
  have hXN : X ≤ Subgroup.normalizer (N : Set Y) := hXle.trans hNN
  set F := X ⊔ N with hF
  set E := F ⊓ P with hE
  have hEN : E ≤ Subgroup.normalizer (N : Set Y) := inf_le_right.trans hPN
  have hFE : F ≤ E ⊔ N := by
    intro f hf
    have hf' : f ∈ ((P ⊔ N : Subgroup Y) : Set Y) := sup_le hXle le_sup_right hf
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P N hPN] at hf'
    obtain ⟨q, hq, m, hm, rfl⟩ := hf'
    have hqF : q ∈ F := by
      have := F.mul_mem hf (F.inv_mem ((le_sup_right : N ≤ F) hm))
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hqF, hq⟩) (Subgroup.mem_sup_right hm)
  have hEodd : Odd (Nat.card E) := hP.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hcard : Nat.card X = Nat.card E := by
    have h1 := E2.BorelLift.card_sup_mul_card_inf hXN
    have h2 := E2.BorelLift.card_sup_mul_card_inf hEN
    rw [E2.BorelLift.inf_eq_bot_of_odd hX hN, Subgroup.card_bot, mul_one] at h1
    rw [E2.BorelLift.inf_eq_bot_of_odd hEodd hN, Subgroup.card_bot, mul_one] at h2
    have heq : E ⊔ N = F := le_antisymm (sup_le (inf_le_left) le_sup_right) hFE
    rw [heq] at h2
    rw [← hF] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.symm.trans h2)
  obtain ⟨n, hn, hXeq⟩ := E2.BorelLift.exists_conj_of_card_eq hN hEodd hEN
    ((le_sup_left : X ≤ F).trans hFE) hcard
  refine ⟨n, hn, ?_⟩
  rw [hXeq]
  rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have : n * (n⁻¹ * e * n⁻¹⁻¹) * n⁻¹ = e := by group
  rw [this]
  exact he.2

theorem not_le_of_case_one {H S MH K B A : Subgroup Γ} {n : ℕ} {t : Γ}
    (hmin : MinParabolic H S MH) (hK : K ∈ cComp H) (hHK : H = K ⊔ S)
    (hJ : kerIn MH H = pCoreOf 2 H) (ht : t ∈ S)
    (hMeq : MH = MH ⊓ K ⊔ cjSub t (MH ⊓ K) ⊔ S) (hn : 2 ≤ n)
    (hty : IsPSL 2 2 n ↥(E2.star MH H K) ∨ IsSz n ↥(E2.star MH H K))
    (hB : E2.IsBorelIn (E2.star MH H K) (E2.star MH H (MH ⊓ K)))
    (hBM : B ≤ MH) (hBo : Odd (Nat.card B)) (hAB : A ≤ B) :
    ¬ H ⊓ Subgroup.normalizer (A : Set Γ) ≤ MH := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf S H := hmin.isSylow
  have hTM : S ≤ MH := hmin.le
  have hMH : MH ≤ H := hmin.maximal.1.le
  set Q : Subgroup Γ := pCoreOf 2 H with hQ
  have hQT : Q ≤ S := E2.BorelLift.pCoreOf_le_of_sylow hT
  have hJS : kerIn MH H ≤ S := hJ ▸ hQT
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  have hsimple : IsSimpleGroup ↥(E2.star MH H K) := by
    rcases hty with h | h
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n h).2
    · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 n h).2
  have hsub : ∀ {X Y : Subgroup Γ}, X ≤ Y → E2.star MH H X ≤ E2.star MH H Y :=
    fun h => Subgroup.map_mono fun x hx => h hx
  set R := oTwoUpper H with hRdef
  have hReq : R = conjClosure K S := E2.BorelLift.oTwoUpper_eq_conjClosure_T hperf hT.2.1 hHK
  have hKR : K ≤ R := hReq ▸ le_conjClosure K S
  set π := starPi MH H with hπ
  set Ks := E2.star MH H K with hKs
  set SK := E2.star MH H (S ⊓ K) with hSK
  have hTNR : S ≤ Subgroup.normalizer ((S ⊓ R : Subgroup Γ) : Set Γ) := by
    intro v hv
    have hvR : v ∈ Subgroup.normalizer (R : Set Γ) := le_normalizer_oTwoUpper H (hT.1 hv)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxR⟩
      exact ⟨S.mul_mem (S.mul_mem hv hxT) (S.inv_mem hv),
        (Subgroup.mem_normalizer_iff.mp hvR x).mp hxR⟩
    · rintro ⟨hxT, hxR⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hvR x).mpr hxR⟩
      have := S.mul_mem (S.mul_mem (S.inv_mem hv) hxT) hv
      simpa [mul_assoc] using this
  have hAK := E2.BorelLift.inf_le_normalizer_one hT hTM hK hHK hJ hsimple hB
  have hMS : MH ≤ Subgroup.normalizer ((S ⊓ R : Subgroup Γ) : Set Γ) := by
    rw [hMeq]
    refine sup_le (sup_le hAK ?_) hTNR
    rintro _ ⟨m, hm, rfl⟩
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTNR ht) (hAK hm))
      (Subgroup.inv_mem _ (hTNR ht))
    simpa [MulAut.conj_apply] using this
  have hcjR : ∀ u ∈ S, cjSub u K ≤ R := by
    intro u hu x hx
    rw [hReq]
    have hx' := mem_cjSub.mp hx
    have := mem_conjClosure hu hx'
    simpa [mul_assoc] using this
  set Xc : Set Γ := {x | ∃ u ∈ S, x ∈ MH ∧ x ∈ cjSub u K} with hXc
  set X : Set Γ := Xc ∪ ((S ⊓ R : Subgroup Γ) : Set Γ) with hX
  set N₁ : Subgroup Γ := Subgroup.closure Xc with hN₁
  have hN₁R : N₁ ≤ R := (Subgroup.closure_le _).mpr fun x ⟨u, hu, _, hxK⟩ => hcjR u hu hxK
  have hTN₁ : S ≤ Subgroup.normalizer (N₁ : Set Γ) := by
    intro v hv
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    have hle : N₁.map (MulAut.conj v).toMonoidHom ≤ N₁ := by
      rw [hN₁, MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨y, ⟨u, hu, hyM, hyK⟩, rfl⟩
      refine ⟨v * u, S.mul_mem hv hu, ?_, ?_⟩
      · exact MH.mul_mem (MH.mul_mem (hTM hv) hyM) (MH.inv_mem (hTM hv))
      · rw [mem_cjSub]
        have := mem_cjSub.mp hyK
        simpa [MulAut.conj_apply, mul_assoc] using this
    exact hle ⟨x, hx, rfl⟩
  have hMN₁ : MH ≤ N₁ ⊔ S := by
    have h1 : MH ⊓ K ≤ N₁ := fun x hx =>
      Subgroup.subset_closure ⟨1, S.one_mem, hx.1, by rw [mem_cjSub]; simpa using hx.2⟩
    have h2 : cjSub t (MH ⊓ K) ≤ N₁ := by
      rintro _ ⟨m, hm, rfl⟩
      refine Subgroup.subset_closure ⟨t, ht, ?_, ?_⟩
      · exact MH.mul_mem (MH.mul_mem (hTM ht) hm.1) (MH.inv_mem (hTM ht))
      · rw [mem_cjSub]
        simpa [MulAut.conj_apply, mul_assoc] using hm.2
    rw [hMeq]
    exact sup_le (sup_le (h1.trans le_sup_left) (h2.trans le_sup_left)) le_sup_right
  have hPX : MH ⊓ R ≤ Subgroup.closure X := by
    intro m hm
    have hm' : m ∈ ((N₁ ⊔ S : Subgroup Γ) : Set Γ) := hMN₁ hm.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N₁ S hTN₁] at hm'
    obtain ⟨a, ha, s, hs, rfl⟩ := hm'
    have hsR : s ∈ R := by
      have := R.mul_mem (R.inv_mem (hN₁R ha)) hm.2
      simpa using this
    have h1 : N₁ ≤ Subgroup.closure X := Subgroup.closure_mono Set.subset_union_left
    exact (Subgroup.closure X).mul_mem (h1 ha) (Subgroup.subset_closure (Or.inr ⟨hs, hsR⟩))
  have hSKsyl : IsSylowTwoOf SK Ks := E2.BorelLift.sylow_star hT hK
  have hbor : E2.star MH H (MH ⊓ K) = Ks ⊓ Subgroup.normalizer (SK : Set (E2.StarQuot MH H)) :=
    E2.BorelLift.borel_eq hT hTM hK hB
  have hSKM : SK ≤ Ks ⊓ Subgroup.normalizer (SK : Set (E2.StarQuot MH H)) :=
    le_inf hSKsyl.1 Subgroup.le_normalizer
  have hSKodd : Odd (SK.relIndex (Ks ⊓ Subgroup.normalizer (SK : Set (E2.StarQuot MH H)))) := by
    have h1 : IsSylowTwoOf SK (Ks ⊓ Subgroup.normalizer (SK : Set (E2.StarQuot MH H))) :=
      A4.isSylowTwoOf_mono hSKsyl hSKM inf_le_left
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact h1.2.2
  obtain ⟨C, hCM, hCcard, hCS⟩ := E2.BorelLift.exists_complement hSKM (fun x hx => hx.2)
    hSKsyl.2.1 hSKodd
  have hCN : C ≤ Subgroup.normalizer (SK : Set (E2.StarQuot MH H)) := hCM.trans inf_le_right
  have hCK : C ≤ Ks := hCM.trans inf_le_left
  have hCodd : Odd (Nat.card C) := hCcard ▸ hSKodd
  have hNC : Ks ⊓ Subgroup.normalizer (SK : Set (E2.StarQuot MH H)) ≤ C ⊔ SK := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hCM hSKM) ?_).ge
    have h1 := E2.BorelLift.card_sup_mul_card_inf hCN
    rw [hCS, Subgroup.card_bot, mul_one] at h1
    rw [h1, hCcard]
    have h2 := Subgroup.relIndex_mul_card SK (Ks ⊓ Subgroup.normalizer (SK : Set _))
    rw [inf_eq_left.mpr hSKM] at h2
    rw [h2]
  have hInv : CartanInv ↥Ks := by
    rcases hty with h | h
    · exact cartanInv_of_isPSL2 (by omega) h
    · exact cartanInv_of_isSz h
  obtain ⟨hCab, wK, hwKK, hwKN, hwKinv⟩ := invOut_rel hInv hSKsyl hCK hCN hNC hCS
  set Lc : Γ → Subgroup (E2.StarQuot MH H) := fun u => E2.star MH H (cjSub u K) with hLc
  have hcomp : ∀ u ∈ S, CFSG.IsComponent (Lc u) := fun u hu =>
    E2.BorelLift.isComponent_star_cjSub hK hJ hsimple (hT.1 hu)
  have hLcomm : ∀ u ∈ S, ∀ v ∈ S, Lc u ≠ Lc v → ∀ x ∈ Lc u, ∀ y ∈ Lc v, x * y = y * x := by
    intro u hu v hv hne x hx y hy
    rcases CFSG.LocalCores.distinct_components_commute (hcomp u hu) (hcomp v hv) with h | h
    · exact absurd h hne
    · have h1 := Subgroup.commutator_mem_commutator hx hy
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
  have hLcmap : ∀ u (hu : u ∈ S), Lc u = Ks.map (MulAut.conj (π ⟨u, hT.1 hu⟩)).toMonoidHom :=
    fun u hu => star_cjSub_eq (hT.1 hu)
  have hLc1 : Lc 1 = Ks := by
    show E2.star MH H (cjSub 1 K) = E2.star MH H K
    rw [cjSub_one]
  have hLN : ∀ u ∈ S, Lc u ≤ Subgroup.normalizer (Ks : Set (E2.StarQuot MH H)) := by
    intro u hu
    by_cases he : Lc u = Ks
    · rw [he]
      exact Subgroup.le_normalizer
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hc : ∀ z ∈ Ks, x * z = z * x := fun z hz =>
        hLcomm u hu 1 S.one_mem (by rwa [hLc1]) x hx z (by rwa [hLc1])
      constructor
      · intro hy
        rw [hc y hy, mul_inv_cancel_right]
        exact hy
      · intro hy
        have h1 := hc _ hy
        have h2 : y = x * y * x⁻¹ := by
          calc y = x⁻¹ * ((x * y * x⁻¹) * x) := by group
            _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [h1]
            _ = x * y * x⁻¹ := by group
        rw [h2]
        exact hy
  have hex : ∀ L : Subgroup (E2.StarQuot MH H), (∃ u ∈ S, L = Lc u) →
      ∃ u : ↥H, (u : Γ) ∈ S ∧ L = Lc u := by
    rintro L ⟨u, hu, rfl⟩
    exact ⟨⟨u, hT.1 hu⟩, hu, rfl⟩
  set uH : Subgroup (E2.StarQuot MH H) → ↥H := fun L =>
    if h : ∃ u ∈ S, L = Lc u then (hex L h).choose else 1 with huH
  have huH_spec : ∀ L, (∃ u ∈ S, L = Lc u) → ((uH L : Γ) ∈ S ∧ L = Lc (uH L)) := by
    intro L h
    rw [show uH L = (hex L h).choose from dite_eq_left h]
    exact (hex L h).choose_spec
  set D : Subgroup (E2.StarQuot MH H) → Subgroup (E2.StarQuot MH H) := fun L =>
    C.map (MulAut.conj (π (uH L))).toMonoidHom with hD
  set w : Subgroup (E2.StarQuot MH H) → E2.StarQuot MH H := fun L =>
    π (uH L) * wK * (π (uH L))⁻¹ with hw
  set 𝒦 : Finset (Subgroup (E2.StarQuot MH H)) :=
    (Set.toFinite {L : Subgroup (E2.StarQuot MH H) | ∃ u ∈ S, L = Lc u}).toFinset with h𝒦
  have hmem𝒦 : ∀ L, L ∈ 𝒦 ↔ ∃ u ∈ S, L = Lc u := fun L => by
    rw [h𝒦, Set.Finite.mem_toFinset]
    rfl
  have hLeq : ∀ L ∈ 𝒦, L = Ks.map (MulAut.conj (π (uH L))).toMonoidHom := by
    intro L hL
    obtain ⟨hu, hLu⟩ := huH_spec L ((hmem𝒦 L).mp hL)
    exact hLu.trans (hLcmap _ hu)
  have hcomm𝒦 : ∀ L ∈ 𝒦, ∀ L' ∈ 𝒦, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x := by
    intro L hL L' hL' hne x hx y hy
    obtain ⟨u, hu, rfl⟩ := (hmem𝒦 L).mp hL
    obtain ⟨u', hu', rfl⟩ := (hmem𝒦 L').mp hL'
    exact hLcomm u hu u' hu' hne x hx y hy
  have hDL : ∀ L ∈ 𝒦, D L ≤ L := fun L hL =>
    (Subgroup.map_mono hCK).trans (hLeq L hL).ge
  have hDab : ∀ L ∈ 𝒦, ∀ a ∈ D L, ∀ b ∈ D L, a * b = b * a := by
    rintro L - _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hCab a ha b hb]
  have hwL : ∀ L ∈ 𝒦, w L ∈ L := fun L hL => (hLeq L hL).ge ⟨wK, hwKK, rfl⟩
  have hwinv : ∀ L ∈ 𝒦, ∀ d ∈ D L, w L * d * (w L)⁻¹ = d⁻¹ := by
    rintro L - _ ⟨d, hd, rfl⟩
    simp only [hw, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc π (uH L) * wK * (π (uH L))⁻¹ * (π (uH L) * d * (π (uH L))⁻¹) *
          (π (uH L) * wK * (π (uH L))⁻¹)⁻¹ = π (uH L) * (wK * d * wK⁻¹) * (π (uH L))⁻¹ := by
          group
      _ = (π (uH L) * d * (π (uH L))⁻¹)⁻¹ := by rw [hwKinv d hd]; group
  obtain ⟨x₀, hx₀, hx₀act⟩ := exists_mul_of_finset 𝒦 hcomm𝒦 w hwL
  obtain ⟨hPab, hPinv⟩ := inv_mem_of_iSup hcomm𝒦 D w hDL hDab hwinv hx₀act
  set P : Subgroup (E2.StarQuot MH H) := ⨆ L ∈ 𝒦, D L with hPdef
  set SR := E2.star MH H (S ⊓ R) with hSR
  have hstarS : ∀ u ∈ S, E2.star MH H (S ⊓ cjSub u K) = E2.star MH H S ⊓ Lc u :=
    fun u _ => star_inf_eq hJS
  have hborel_u : ∀ u ∈ S, E2.star MH H (MH ⊓ cjSub u K) ≤ D (Lc u) ⊔ E2.star MH H S ⊓ Lc u := by
    intro u hu
    have hL𝒦 : Lc u ∈ 𝒦 := (hmem𝒦 _).mpr ⟨u, hu, rfl⟩
    obtain ⟨hv, hLv⟩ := huH_spec (Lc u) ⟨u, hu, rfl⟩
    set v := uH (Lc u) with hvdef
    have hconj : ∀ (z : ↥H), (z : Γ) ∈ S →
        E2.star MH H (MH ⊓ cjSub z K) =
          (Ks ⊓ Subgroup.normalizer (SK : Set (E2.StarQuot MH H))).map
            (MulAut.conj (π z)).toMonoidHom ∧
        E2.star MH H S ⊓ Lc z = SK.map (MulAut.conj (π z)).toMonoidHom := by
      intro z hz
      have hzM : (z : Γ) ∈ MH := hTM hz
      have hcjM : cjSub (z : Γ) (MH ⊓ K) = MH ⊓ cjSub (z : Γ) K := by
        ext x
        simp only [mem_cjSub, Subgroup.mem_inf]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          have := MH.mul_mem (MH.mul_mem hzM h1) (MH.inv_mem hzM)
          simpa [mul_assoc] using this
        · rintro ⟨h1, h2⟩
          exact ⟨MH.mul_mem (MH.mul_mem (MH.inv_mem hzM) h1) hzM, h2⟩
      have hcjS : cjSub (z : Γ) (S ⊓ K) = S ⊓ cjSub (z : Γ) K := by
        ext x
        simp only [mem_cjSub, Subgroup.mem_inf]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          have := S.mul_mem (S.mul_mem hz h1) (S.inv_mem hz)
          simpa [mul_assoc] using this
        · rintro ⟨h1, h2⟩
          exact ⟨S.mul_mem (S.mul_mem (S.inv_mem hz) h1) hz, h2⟩
      refine ⟨?_, ?_⟩
      · rw [← hcjM, star_cjSub_eq z.2, hbor]
      · rw [← hstarS z hz, ← hcjS, star_cjSub_eq z.2]
    obtain ⟨h1, h2⟩ := hconj ⟨u, hT.1 hu⟩ hu
    obtain ⟨-, h3⟩ := hconj v hv
    have hSL : E2.star MH H S ⊓ Lc u = E2.star MH H S ⊓ Lc v := by rw [← hLv]
    have hB1 : E2.star MH H (MH ⊓ cjSub u K) = Lc u ⊓ Subgroup.normalizer
        ((E2.star MH H S ⊓ Lc u : Subgroup _) : Set (E2.StarQuot MH H)) := by
      rw [h1, h2, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
        Subgroup.map_equiv_normalizer_eq, ← hLcmap u hu]
    have hB2 : Lc v ⊓ Subgroup.normalizer
        ((E2.star MH H S ⊓ Lc v : Subgroup _) : Set (E2.StarQuot MH H)) ≤
          D (Lc u) ⊔ (E2.star MH H S ⊓ Lc v) := by
      rw [h3, hLcmap _ hv, ← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_inf_eq _ _ _
        (MulAut.conj _).injective]
      have := Subgroup.map_mono (f := (MulAut.conj (π v)).toMonoidHom) hNC
      rw [Subgroup.map_sup] at this
      exact this
    rw [hB1, hSL, ← hLv]
    rw [← hLv] at hB2
    exact hB2
  have hstarMR : E2.star MH H (MH ⊓ R) ≤ P ⊔ SR := by
    set Φ : Subgroup Γ := ((P ⊔ SR).comap π).map H.subtype with hΦ
    have hXΦ : Subgroup.closure X ≤ Φ := by
      rw [Subgroup.closure_le]
      rintro x (⟨u, hu, hxM, hxK⟩ | ⟨hxS, hxR⟩)
      · have hxH : x ∈ H := hMH hxM
        refine ⟨⟨x, hxH⟩, ?_, rfl⟩
        have h1 : π ⟨x, hxH⟩ ∈ E2.star MH H (MH ⊓ cjSub u K) := starPi_mem_star ⟨hxM, hxK⟩
        have h2 := hborel_u u hu h1
        have hL𝒦 : Lc u ∈ 𝒦 := (hmem𝒦 _).mpr ⟨u, hu, rfl⟩
        have hDP : D (Lc u) ≤ P := le_iSup₂_of_le (f := fun L (_ : L ∈ 𝒦) => D L) (Lc u) hL𝒦 le_rfl
        have hSP : E2.star MH H S ⊓ Lc u ≤ SR := by
          rw [← hstarS u hu]
          exact hsub (inf_le_inf_left S (hcjR u hu))
        exact (sup_le_sup hDP hSP) h2
      · have hxH : x ∈ H := hT.1 hxS
        exact ⟨⟨x, hxH⟩, Subgroup.mem_sup_right (starPi_mem_star ⟨hxS, hxR⟩), rfl⟩
    intro y hy
    obtain ⟨h, hh, rfl⟩ := mem_star510_iff.mp hy
    obtain ⟨h', hh', hhe⟩ := hXΦ (hPX hh)
    have : h' = h := Subtype.ext hhe
    rw [← this]
    exact hh'
  have hRidx : ∃ k : ℕ, R.relIndex H = 2 ^ k := by
    have hHR : H = R ⊔ S := le_antisymm (hHK ▸ sup_le_sup_right hKR S)
      (sup_le (oTwoUpper_le H) hT.1)
    have hSRn : S ≤ Subgroup.normalizer (R : Set Γ) := fun s hs =>
      le_normalizer_oTwoUpper H (hT.1 hs)
    have h1 : R.relIndex (S ⊔ R) = R.relIndex S := A4.relIndex_sup_eq_of_le_normalizer' hSRn
    rw [sup_comm, ← hHR] at h1
    obtain ⟨m, hm⟩ := hT.2.1.exists_card_eq
    exact E2.BorelLift.exists_eq_two_pow_of_dvd (h1 ▸ hm ▸ Subgroup.relIndex_dvd_card R S)
  obtain ⟨kR, hkR⟩ := hRidx
  have hBR : B ≤ R := E2.BorelLift.le_of_odd (oTwoUpper_le H) (le_normalizer_oTwoUpper H) hkR
    (hBM.trans hMH) hBo
  set Bs := E2.star MH H B with hBs
  have hBsle : Bs ≤ P ⊔ SR := (hsub (le_inf hBM hBR)).trans hstarMR
  have hBBs : Nat.card Bs = Nat.card B := by
    have hinj : Function.Injective (π.comp (Subgroup.inclusion (hBM.trans hMH))) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro b hb
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, starPi_eq_one_iff] at hb
      have hbQ : (b : Γ) ∈ B ⊓ Q := ⟨b.2, hJ ▸ hb⟩
      rw [E2.BorelLift.inf_eq_bot_of_odd hBo (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H),
        Subgroup.mem_bot] at hbQ
      exact Subgroup.mem_bot.mpr (Subtype.ext hbQ)
    have hrange : Bs = (π.comp (Subgroup.inclusion (hBM.trans hMH))).range := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hy
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨b, rfl⟩
        exact starPi_mem_star b.2
    rw [hrange, ← Nat.card_range_of_injective hinj]
    rfl
  have hDodd : ∀ L ∈ 𝒦, ∀ d ∈ D L, Odd (orderOf d) := by
    rintro L - _ ⟨c, hc, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
    have := orderOf_dvd_natCard (⟨c, hc⟩ : C)
    rw [Subgroup.orderOf_mk] at this
    exact hCodd.of_dvd_nat this
  have hPodd' : ∀ x ∈ P, Odd (orderOf x) := by
    let V : Subgroup (E2.StarQuot MH H) :=
      { carrier := {x | x ∈ P ∧ Odd (orderOf x)}
        one_mem' := ⟨Subgroup.one_mem _, by rw [orderOf_one]; exact odd_one⟩
        mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
          have hc : Commute a b := hPab a ha.1 b hb.1
          exact Odd.of_dvd_nat (Nat.odd_mul.2 ⟨ha.2, hb.2⟩)
            (hc.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))⟩
        inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by rw [orderOf_inv]; exact ha.2⟩ }
    have hPV : P ≤ V := iSup₂_le fun L hL d hd =>
      ⟨le_iSup₂_of_le (f := fun L (_ : L ∈ 𝒦) => D L) L hL le_rfl hd, hDodd L hL d hd⟩
    exact fun x hx => (hPV hx).2
  have hPodd : Odd (Nat.card P) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 (even_iff_two_dvd.mp hev)
    have h1 := hPodd' z z.2
    rw [Subgroup.orderOf_coe, hz] at h1
    exact absurd h1 (by decide)
  have hPM : P ≤ E2.star MH H MH := by
    refine iSup₂_le fun L hL => ?_
    rintro _ ⟨c, hc, rfl⟩
    have hcM : c ∈ E2.star MH H MH := by
      have := (hCM.trans (hbor ▸ le_rfl : Ks ⊓ _ ≤ E2.star MH H (MH ⊓ K))) hc
      exact hsub inf_le_left this
    have huM : π (uH L) ∈ E2.star MH H MH := by
      obtain ⟨hu, -⟩ := huH_spec L ((hmem𝒦 L).mp hL)
      exact starPi_mem_star (hTM hu)
    show π (uH L) * c * (π (uH L))⁻¹ ∈ _
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ huM hcM) (Subgroup.inv_mem _ huM)
  have hSR2 : IsPGroup 2 SR := by
    have h1 : IsPGroup 2 ((S ⊓ R).subgroupOf H) := (hT.2.1.to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hT.1)).symm
    exact h1.map _
  have hMsN : E2.star MH H MH ≤ Subgroup.normalizer (SR : Set (E2.StarQuot MH H)) := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := mem_star510_iff.mp hy
    exact starPi_mem_normalizer (hMS hm)
  have hPN : P ≤ Subgroup.normalizer (SR : Set (E2.StarQuot MH H)) := hPM.trans hMsN
  set As := E2.star MH H A with hAs
  have hAodd : Odd (Nat.card A) := hBo.of_dvd_nat (Subgroup.card_dvd_of_le hAB)
  have hAsodd : Odd (Nat.card As) := by
    have h1 : Nat.card As ∣ Nat.card (A.subgroupOf H) := Subgroup.card_map_dvd _ _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAB.trans (hBM.trans hMH))).toEquiv] at h1
    exact hAodd.of_dvd_nat h1
  have hAsle : As ≤ P ⊔ SR := (hsub hAB).trans hBsle
  obtain ⟨m, hmSR, hmA⟩ := exists_conj_le_of_le_sup hSR2 hPodd hPN hAsodd hAsle
  have hKs𝒦 : Ks ∈ 𝒦 := (hmem𝒦 Ks).mpr ⟨1, S.one_mem, hLc1.symm⟩
  have hx₀N : x₀ ∈ Subgroup.normalizer (Ks : Set (E2.StarQuot MH H)) := by
    have hle : (⨆ L ∈ 𝒦, L) ≤ Subgroup.normalizer (Ks : Set (E2.StarQuot MH H)) := by
      refine iSup₂_le fun L hL => ?_
      obtain ⟨u, hu, rfl⟩ := (hmem𝒦 L).mp hL
      exact hLN u hu
    exact hle hx₀
  have hSKeq : SK = E2.star MH H S ⊓ Ks := star_inf_eq hJS
  have hSRK : SR ⊓ Ks = SK := by
    have hle : SK ≤ SR ⊓ Ks := le_inf (hsub (inf_le_inf_left S hKR)) hSKsyl.1
    refine le_antisymm ?_ hle
    exact (A4.isSylowTwoOf_iff_maximal.1 hSKsyl).2.2 _ inf_le_right
      (hSR2.to_le inf_le_left) hle
  have hx₀M : x₀ ∉ E2.star MH H MH := by
    intro hx
    have h1 : x₀ ∈ Subgroup.normalizer ((SR ⊓ Ks : Subgroup _) : Set (E2.StarQuot MH H)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hMsN hx) y,
        Subgroup.mem_normalizer_iff.mp hx₀N y]
    rw [hSRK] at h1
    obtain ⟨hcS, hcL⟩ := huH_spec Ks ⟨1, S.one_mem, hLc1.symm⟩
    set c := π (uH Ks) with hc
    have hcK : Ks.map (MulAut.conj c).toMonoidHom = Ks := by
      rw [← hLcmap _ hcS]
      exact hcL.symm
    have hcN : c ∈ Subgroup.normalizer (SK : Set (E2.StarQuot MH H)) := by
      have hcKs : c ∈ Subgroup.normalizer (Ks : Set (E2.StarQuot MH H)) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcK
      have hcS' : c ∈ Subgroup.normalizer (E2.star MH H S : Set (E2.StarQuot MH H)) :=
        Subgroup.le_normalizer (starPi_mem_star hcS)
      rw [hSKeq, Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hcS' y,
        Subgroup.mem_normalizer_iff.mp hcKs y]
    have hwN : w Ks ∈ Subgroup.normalizer (SK : Set (E2.StarQuot MH H)) := by
      refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
      rw [← hx₀act Ks hKs𝒦 y (hSKsyl.1 hy)]
      exact (Subgroup.mem_normalizer_iff.mp h1 y).mp hy
    apply hwKN
    have : wK = c⁻¹ * w Ks * c := by
      simp only [hw, hc]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hcN) hwN) hcN
  set g := m⁻¹ * x₀ * m with hg
  have hmM : m ∈ E2.star MH H MH := hsub (inf_le_left.trans hTM) hmSR
  have hgM : g ∉ E2.star MH H MH := by
    intro h
    apply hx₀M
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hmM h) (Subgroup.inv_mem _ hmM)
    simpa [hg, mul_assoc] using this
  have hgA : ∀ a ∈ As, g * a * g⁻¹ = a⁻¹ := by
    intro a ha
    have h1 : m * a * m⁻¹ ∈ P := hmA ⟨a, ha, rfl⟩
    have h2 := hPinv _ h1
    calc g * a * g⁻¹ = m⁻¹ * (x₀ * (m * a * m⁻¹) * x₀⁻¹) * m := by rw [hg]; group
      _ = m⁻¹ * (m * a * m⁻¹)⁻¹ * m := by rw [h2]
      _ = a⁻¹ := by group
  obtain ⟨g₀, hg₀⟩ := starPi_surjective MH H g
  rw [← hg₀] at hgM hgA
  have hg₀M : (g₀ : Γ) ∉ MH := fun h => hgM (starPi_mem_star h)
  refine not_le_of_conj_mem_sup g₀.2 hg₀M (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
    (hQT.trans hTM) hMH ?_ hAodd ?_
  · exact (hAB.trans (hBM.trans hMH)).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  · intro a ha
    have haH : a ∈ H := hBM.trans hMH (hAB ha)
    have h1 := hgA (π ⟨a, haH⟩) (starPi_mem_star ha)
    have h2 : π (g₀ * ⟨a, haH⟩ * g₀⁻¹) = π ⟨a, haH⟩⁻¹ := by
      rw [map_mul, map_mul, map_inv, h1, map_inv]
    have h3 := starPi_eq_iff.mp h2.symm
    rw [hJ] at h3
    have h4 : (a⁻¹ : Γ)⁻¹ * ((g₀ : Γ) * a * (g₀ : Γ)⁻¹) ∈ Q := by simpa using h3
    have h5 : (g₀ : Γ) * a * (g₀ : Γ)⁻¹ = a⁻¹ * ((a⁻¹ : Γ)⁻¹ * ((g₀ : Γ) * a * (g₀ : Γ)⁻¹)) := by
      group
    rw [h5]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (A.inv_mem ha)) (Subgroup.mem_sup_right h4)

end CFSG.Quasithin.H13.KG4413
