module

public import CFSG.Quasithin.Vol2.E2SevenPairN
public import CFSG.Quasithin.Vol2.E2Eleven
public import CFSG.Quasithin.Vol2.Ch8Sec2L825H

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs

section L822B

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ch82ZI_le_centralizer_822 {V : Subgroup G} {h : G} (hV : IsElemAbelian 2 V) :
    ch82ZI V h ≤ Subgroup.centralizer (ch82I V h : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  have hVh : IsElemAbelian 2 (B6.conjSub h V) := by
    rw [conjSub_eq_conjSubgroup_82]
    exact isElemAbelian_conjSubgroup hV _
  refine sup_le (fun v hv => ?_) (fun w hw => ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := hV.1
    exact setLike_mul_comm (hz.1 : z ∈ V) hv
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := hVh.1
    exact setLike_mul_comm (hz.2 : z ∈ B6.conjSub h V) hw

omit [Finite G] in
theorem cases_822 {H T M V I : Subgroup G} (hIC : IsInIHTVC H T (H ⊓ M) V I)
    (hSp : ∀ k : ℕ, ¬ IsSp4C k (E2.StarQuot (H ⊓ M ⊓ I) I)) :
    ∃ k : ℕ, (∃ m : ℕ, E1.nParam H = ((k * m : ℕ) : ℕ∞)) ∧
      ((k = 1 ∧ ∃ m : ℕ, Odd m ∧ 1 < m ∧ Nonempty (E2.StarQuot (M ⊓ I) I ≃* DihedralGroup m)) ∨
        IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) ∧
      (1 < k → E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I))) := by
  have hMI := inf_inf_eq_82 (M := M) hIC.1
  obtain ⟨-, -, -, -, k, hk, hc⟩ := hIC
  refine ⟨k, hk, ?_⟩
  rw [← hMI]
  rcases hc with ⟨-, hPS, hB⟩ | ⟨hk1, p, a, hp, hp2, ha, ⟨e⟩⟩ | ⟨-, -, hS, -⟩
  · exact ⟨Or.inr hPS, fun _ => hB⟩
  · refine ⟨Or.inl ⟨hk1, p ^ a, (hp.eq_two_or_odd'.resolve_left hp2).pow,
      Nat.one_lt_pow (by omega) hp.one_lt, ⟨e⟩⟩, fun h1 => absurd hk1 (by omega)⟩
  · exact absurd hS (hSp k)

theorem e214_822 (hE214 : AS_E_2_14) {H T M V : Subgroup G} {h : G}
    (hhI : h ∈ ch82I V h) (hIC : IsInIHTVC H T (H ⊓ M) V (ch82I V h)) (hZ1 : ch82ZI V h ≠ ⊥)
    (h28 : E2.Hyp28 H T (H ⊓ M) V) (hchar : QuasithinUnique.CharTwo H)
    (hTI : IsTISetIn V (H ⊓ M)) (hDLSz : IsDihL2Sz (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))) :
    M ⊓ ch82I V h = ch82I V h ⊓ Subgroup.normalizer (V : Set G) ∧
      E2.star (M ⊓ ch82I V h) (ch82I V h) V =
        E2.star (M ⊓ ch82I V h) (ch82I V h) (T ⊓ ch82I V h) ⊓
          Subgroup.centralizer (E2.star (M ⊓ ch82I V h) (ch82I V h) (T ⊓ ch82I V h) :
            Set (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))) := by
  have hMI := inf_inf_eq_82 (M := M) hIC.1
  obtain ⟨h1, ⟨-, hV⟩, -⟩ :=
    hE214 G H T (H ⊓ M) V (ch82I V h) h h28 hchar hTI hIC hhI rfl hZ1
      (isDihL2Sz_of_eq hMI.symm hDLSz)
  refine ⟨hMI ▸ h1, ?_⟩
  rw [← hMI]
  exact hV

theorem star_eq_normalizer_of_borel_822 {T M I : Subgroup G} (hTM : T ⊓ I ≤ M ⊓ I)
    (hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ I) I)
    (hB : E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I))) :
    E2.star (M ⊓ I) I (M ⊓ I) =
      Subgroup.normalizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
  obtain ⟨S, hSsyl, hSeq⟩ := hB
  have hTM' : E2.star (M ⊓ I) I (T ⊓ I) ≤ E2.star (M ⊓ I) I (M ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hTM)
  have hSB : S ≤ E2.star (M ⊓ I) I (M ⊓ I) := by
    rw [hSeq]
    exact le_inf le_top Subgroup.le_normalizer
  have hBN : E2.star (M ⊓ I) I (M ⊓ I) ≤ Subgroup.normalizer (S : Set (E2.StarQuot (M ⊓ I) I)) :=
    by rw [hSeq]; exact inf_le_right
  have hTS : E2.star (M ⊓ I) I (T ⊓ I) ≤ S :=
    E2.le_of_normal_sylow' (B6.isSylowTwoOf_mono hSsyl hSB le_top) hBN hTM' hS.2.1
  have hTeq : E2.star (M ⊓ I) I (T ⊓ I) = S := by
    obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj hS hSsyl
    refine Subgroup.eq_of_le_of_card_ge hTS ?_
    rw [hc]
    exact (Subgroup.card_map_of_injective (MulAut.conj c).injective).le
  rw [hSeq, hTeq, top_inf_eq]

theorem dihedral_commute_sr_822 {m : ℕ} (hm : Odd m) {x : DihedralGroup m} {i : ZMod m}
    (hx : x * DihedralGroup.sr i = DihedralGroup.sr i * x) : x = 1 ∨ x = DihedralGroup.sr i := by
  rcases x with j | j
  · left
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at hx
    have h1 : i - j = i + j := DihedralGroup.sr.inj hx
    have h2 : j + j = 0 := by linear_combination -h1
    rw [E2.eq_zero_of_add_self_eq_zero hm h2, DihedralGroup.r_zero]
  · right
    rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr] at hx
    have h1 : i - j = j - i := DihedralGroup.r.inj hx
    have h2 : (j - i) + (j - i) = 0 := by linear_combination -h1
    have h3 := E2.eq_zero_of_add_self_eq_zero hm h2
    rw [sub_eq_zero] at h3
    rw [h3]

omit [Finite G] in
theorem normalizer_le_of_dihedral_822 {Y : Type} [Group Y] {m : ℕ} (hm : Odd m)
    (e : Y ≃* DihedralGroup m) {S : Subgroup Y} (hS2 : ∀ y ∈ S, y * y = 1)
    (hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {s : Y} (hs : s ∈ S) (hs1 : s ≠ 1) :
    Subgroup.normalizer (S : Set Y) ≤ S := by
  intro x hx
  have hxs : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hx s).mp hs
  have hxs1 : x * s * x⁻¹ ≠ 1 := fun h1 => hs1 (by
    have : s = x⁻¹ * (x * s * x⁻¹) * x := by group
    rw [this, h1]
    group)
  have he : e (x * s * x⁻¹) = e s := E2.dihedral_eq_of_commute hm
    (by rw [← map_mul, hS2 _ hxs, map_one]) (by rw [← map_mul, hS2 _ hs, map_one])
    (fun h1 => hxs1 (e.injective (by rw [h1, map_one])))
    (fun h1 => hs1 (e.injective (by rw [h1, map_one])))
    (by rw [← map_mul, ← map_mul, hScomm _ hxs _ hs])
  have hxs' : x * s = s * x := by
    have h1 := e.injective he
    calc x * s = x * s * x⁻¹ * x := by group
      _ = s * x := by rw [h1]
  obtain ⟨i, hi⟩ : ∃ i : ZMod m, e s = DihedralGroup.sr i := by
    rcases hes : e s with j | j
    · exfalso
      have h1 : DihedralGroup.r j * DihedralGroup.r j = 1 := by
        rw [← hes, ← map_mul, hS2 _ hs, map_one]
      rw [DihedralGroup.r_mul_r, DihedralGroup.one_def, DihedralGroup.r.injEq] at h1
      have h2 := E2.eq_zero_of_add_self_eq_zero hm h1
      apply hs1
      apply e.injective
      rw [hes, h2, map_one, DihedralGroup.r_zero]
    · exact ⟨j, rfl⟩
  have hc : e x * DihedralGroup.sr i = DihedralGroup.sr i * e x := by
    rw [← hi, ← map_mul, ← map_mul, hxs']
  rcases dihedral_commute_sr_822 hm hc with h1 | h1
  · have : x = 1 := e.injective (by rw [h1, map_one])
    rw [this]
    exact S.one_mem
  · have : x = s := e.injective (by rw [h1, hi])
    rw [this]
    exact hs

theorem star_eq_normalizer_of_dihedral_822 {T M I : Subgroup G} (hTM : T ⊓ I ≤ M ⊓ I)
    (hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ I) I) {m : ℕ} (hm : Odd m)
    (e : E2.StarQuot (M ⊓ I) I ≃* DihedralGroup m) :
    E2.star (M ⊓ I) I (M ⊓ I) =
      Subgroup.normalizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
  have hTM' : E2.star (M ⊓ I) I (T ⊓ I) ≤ E2.star (M ⊓ I) I (M ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hTM)
  have hcore := E2P.kerIn_star (M ⊓ I) I
  have hM2 : ∀ x ∈ E2.star (M ⊓ I) I (M ⊓ I), x * x = 1 := by
    intro x hx
    rcases hex : e x with i | i
    · have hxk : x ∈ kerIn (E2.star (M ⊓ I) I (M ⊓ I)) ⊤ := by
        intro b _
        rcases heb : e b with j | j
        · have : b * x * b⁻¹ = x := by
            apply e.injective
            rw [map_mul, map_mul, map_inv, heb, hex, DihedralGroup.r_mul_r, DihedralGroup.inv_r,
              DihedralGroup.r_mul_r]
            congr 1
            ring
          rw [this]
          exact hx
        · have : b * x * b⁻¹ = x⁻¹ := by
            apply e.injective
            rw [map_mul, map_mul, map_inv, map_inv, heb, hex, DihedralGroup.sr_mul_r,
              DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
            congr 1
            ring
          rw [this]
          exact (E2.star (M ⊓ I) I (M ⊓ I)).inv_mem hx
      rw [hcore, Subgroup.mem_bot] at hxk
      rw [hxk, one_mul]
    · apply e.injective
      rw [map_mul, hex, DihedralGroup.sr_mul_self, map_one]
  have hMp : IsPGroup 2 (E2.star (M ⊓ I) I (M ⊓ I)) := fun x =>
    ⟨1, Subtype.ext (by simpa [pow_two] using hM2 x x.2)⟩
  have heq : E2.star (M ⊓ I) I (T ⊓ I) = E2.star (M ⊓ I) I (M ⊓ I) := by
    have hS' := hS
    rw [A4.isSylowTwoOf_iff_maximal] at hS'
    exact le_antisymm hTM' (hS'.2.2 _ le_top hMp hTM')
  obtain ⟨s, hs, hs1⟩ : ∃ s ∈ E2.star (M ⊓ I) I (T ⊓ I), s ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : E2.star (M ⊓ I) I (T ⊓ I) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
    have h2 : 2 ∣ Nat.card (E2.StarQuot (M ⊓ I) I) := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      exact dvd_mul_right 2 m
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hidx := hS.2.2
    rw [hbot] at hidx
    apply hidx
    show 2 ∣ Subgroup.relIndex ⊥ ⊤
    rw [Subgroup.relIndex_top_right, Subgroup.index_bot]
    exact h2
  have hle := normalizer_le_of_dihedral_822 hm e (fun y hy => hM2 y (hTM' hy))
    (fun x hx y hy => E2.comm_of_isPGroup_dihedral hm
      (S := (E2.star (M ⊓ I) I (T ⊓ I)).map e.toMonoidHom) (hS.2.1.map _)
      ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ |> fun h1 => e.injective (by rw [map_mul, map_mul]; exact h1))
    hs hs1
  rw [← heq]
  exact le_antisymm Subgroup.le_normalizer hle

omit [Finite G] in
theorem card_star_822 {M' I V : Subgroup G} (hVI : V ≤ I) :
    Nat.card ↥(E2.star M' I V) = (kerIn M' I).relIndex V := by
  rw [E2P.star_def, ← Subgroup.relIndex_ker, E2P.ker_starMap, Subgroup.relIndex_subgroupOf hVI]

theorem card_center_822 {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) {k : ℕ} (hk : 2 ≤ k) (h : IsPSL 2 2 k X ∨ IsSz k X) :
    Nat.card ↥(S ⊓ Subgroup.centralizer (S : Set X)) = 2 ^ k := by
  obtain ⟨j, hB⟩ := E2.exists_fusionBenderBorel_of_psl_or_sz hk h
  have hB' : fusionBenderBorel ↥(⊤ : Subgroup X) (2 ^ k) j :=
    hB.map_mulEquiv Subgroup.topEquiv.symm
  exact (E2.card_inf_centralizer_of_fusionBenderBorel hB' hS).1

omit [Finite G] in
theorem mQuot_add_eq_822 [Finite G] {V P : Subgroup G} {h : G} {k : ℕ}
    (hhP : h ∈ Subgroup.normalizer (P : Set G)) (hidx : P.relIndex V = 2 ^ k)
    (hAC : B6.conjSub h V ⊓ P ⊓ Subgroup.centralizer (V : Set G) = V ⊓ B6.conjSub h V) :
    mQuot (B6.conjSub h V ⊓ P) (B6.conjSub h V ⊓ P ⊓ Subgroup.centralizer (V : Set G)) + k =
      mQuot V (V ⊓ B6.conjSub h V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPh : B6.conjSub h P = P := B6.conjSub_eq_self hhP
  have hidx' : (B6.conjSub h V ⊓ P).relIndex (B6.conjSub h V) = 2 ^ k := by
    rw [Subgroup.inf_relIndex_left, ← hPh]
    have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj h).toMonoidHom) P V
      (MulAut.conj h).injective
    have h2 : (B6.conjSub h P).relIndex (B6.conjSub h V) = P.relIndex V := this
    rw [h2, hidx]
  have e5 : mQuot (B6.conjSub h V) (B6.conjSub h V ⊓ P) = k := by
    unfold mQuot
    rw [hidx', padicValNat.prime_pow]
  have hcard : Nat.card ↥(B6.conjSub h V) = Nat.card ↥V :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have e4 : rk ↥(B6.conjSub h V) = rk ↥V := by
    unfold rk
    rw [hcard]
  rw [hAC]
  have hZA : V ⊓ B6.conjSub h V ≤ B6.conjSub h V ⊓ P := by
    rw [← hAC]
    exact inf_le_left
  have e1 := mQuot_add_rk hZA
  have e2 := mQuot_add_rk (A := B6.conjSub h V) (B := B6.conjSub h V ⊓ P) inf_le_left
  have e3 := mQuot_add_rk (A := V) (B := V ⊓ B6.conjSub h V) inf_le_left
  omega

omit [Finite G] in
theorem ch82U_le_ch82B_822 {V : Subgroup G} {h : G} (hV : IsElemAbelian 2 V)
    (h7 : ∀ x ∈ ch82I V h, (∀ y ∈ (V ⊓ pCoreOf 2 (ch82I V h)) ⊔
        (B6.conjSub h V ⊓ pCoreOf 2 (ch82I V h)),
        x * y * x⁻¹ * y⁻¹ ∈ V ⊓ B6.conjSub h V) → x ∈ pCoreOf 2 (ch82I V h)) :
    ch82U V h ≤ ch82B V h := by
  intro x hx
  refine ⟨hx.1, h7 x ((le_sup_left : V ≤ ch82I V h) hx.1) fun y hy => ?_⟩
  have hle : (V ⊓ pCoreOf 2 (ch82I V h)) ⊔ (B6.conjSub h V ⊓ pCoreOf 2 (ch82I V h)) ≤
      Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun b hb => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have := hV.1
      exact setLike_mul_comm hx.1 hb.1
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ((Subgroup.mem_centralizer_iff.mp hx.2) a ha).symm
  have hxy : x * y = y * x := ((Subgroup.mem_centralizer_iff.mp (hle hy)) x rfl)
  rw [hxy, mul_inv_cancel_right, mul_inv_cancel]
  exact Subgroup.one_mem _

end L822B

end CFSG.Quasithin.H13
