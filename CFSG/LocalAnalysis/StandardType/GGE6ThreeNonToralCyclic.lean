module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralCent
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule
public import CFSG.LieType.AlgebraicGroups.ConnectedConjugationNorm
public import CFSG.LieType.AlgebraicGroups.TorusGroupClosed
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public noncomputable section

namespace CFSG.StandardType.E6NonToralThree

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.Three TableBExc.E6Three

open CFSG.StandardType.NoOffE8Five CFSG.StandardType.NoOffRest

private theorem exists_torus_pow_eq
    {L : Type} [Field L] [IsAlgClosed L] {t : ModGL .E6 L} (ht : t ∈ torusGroup .E6 L)
    {n : ℕ} (hn : 0 < n) :
    ∃ s ∈ torusGroup .E6 L, s ^ n = t := by
  obtain ⟨u, hu⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hroot : ∀ i, ∃ v : Lˣ, v ^ n = u i := by
    intro i
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((u i : Lˣ) : L) hn
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hz
      exact (u i).ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  let u' : Fin Tag.E6.rank → Lˣ := fun i => (hroot i).choose
  have hu' : u' ^ n = u := funext fun i => (hroot i).choose_spec
  refine ⟨rootDiagUnit .E6 u', rootDiagUnit_mem_torusGroup u', ?_⟩
  rw [rootDiagUnit_pow, hu', hu]

private theorem torusGroup_comm
    {L : Type} [Field L] :
    ∀ x y : torusGroup .E6 L, x * y = y * x :=
  fun x y => Subtype.ext ((triangular_borel_structure.{0, 0} .E6 L).1 x x.2 y y.2)

def normPhi
    {L : Type} [Field L] (n : ModGL .E6 L)
    (hnN : n ∈ monomialSubgroup .E6 L) :
    torusGroup .E6 L →* torusGroup .E6 L :=
  Subgroup.normalizerMonoidHom (torusGroup .E6 L)
    ⟨n, mem_normalizer_torusGroup_of_mem_monomialSubgroup hnN⟩

theorem normPhi_apply
    {L : Type} [Field L] (n : ModGL .E6 L)
    (hnN : n ∈ monomialSubgroup .E6 L) (x : torusGroup .E6 L) :
    ((normPhi n hnN x : torusGroup .E6 L) : ModGL .E6 L) =
      n * (x : ModGL .E6 L) * n⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe (torusGroup .E6 L)
    ⟨n, mem_normalizer_torusGroup_of_mem_monomialSubgroup hnN⟩ x

@[expose] def normFun
    {L : Type} [Field L] (φ : torusGroup .E6 L →* torusGroup .E6 L)
    (s : torusGroup .E6 L) : torusGroup .E6 L :=
  s * φ s * φ (φ s)

private theorem normFun_mul
    {L : Type} [Field L] (φ : torusGroup .E6 L →* torusGroup .E6 L)
    (hcomm : ∀ x y : torusGroup .E6 L, x * y = y * x)
    (s t : torusGroup .E6 L) :
    normFun φ (s * t) = normFun φ s * normFun φ t := by
  haveI : IsMulCommutative (torusGroup .E6 L) := ⟨⟨hcomm⟩⟩
  simp only [normFun, map_mul]
  ac_rfl

private theorem normFun_pow
    {L : Type} [Field L] (φ : torusGroup .E6 L →* torusGroup .E6 L)
    (hcomm : ∀ x y : torusGroup .E6 L, x * y = y * x)
    (r : ℕ) (s : torusGroup .E6 L) :
    normFun φ (s ^ r) = normFun φ s ^ r := by
  induction r with
  | zero => simp [normFun]
  | succ r ih => rw [pow_succ, normFun_mul φ hcomm, ih, pow_succ]

private theorem normFun_fixed_n
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    {n : ModGL .E6 L} (hnE : n ∈ E)
    (hTcomm : ∀ x y : torusGroup .E6 L, x * y = y * x)
    (S : torusGroup .E6 L) :
    Commute n (normFun (normPhi n (hEM hnE)) S) := by
  let φ : torusGroup .E6 L →* torusGroup .E6 L := normPhi n (hEM hnE)
  have hn3 : n ^ 3 = 1 := hE.2 n hnE
  have hφ_apply : ∀ x : torusGroup .E6 L,
      ((φ x : torusGroup .E6 L) : ModGL .E6 L) = n * (x : ModGL .E6 L) * n⁻¹ := by
    intro x
    exact Subgroup.normalizerMonoidHom_apply_apply_coe (torusGroup .E6 L)
      ⟨n, mem_normalizer_torusGroup_of_mem_monomialSubgroup (hEM hnE)⟩ x
  have hφ3 : φ (φ (φ S)) = S := by
    apply Subtype.ext
    rw [hφ_apply (φ (φ S)), hφ_apply (φ S), hφ_apply S]
    have hn3' : n * n * n = 1 := by simpa [pow_succ, mul_assoc] using hn3
    calc n * (n * (n * (S : ModGL .E6 L) * n⁻¹) * n⁻¹) * n⁻¹ =
        (n * n * n) * (S : ModGL .E6 L) * (n * n * n)⁻¹ := by group
      _ = S := by rw [hn3']; group
  have hNfix : φ (normFun φ S) = normFun φ S := by
    rw [normFun, map_mul, map_mul, hφ3]
    haveI : IsMulCommutative (torusGroup .E6 L) := ⟨⟨hTcomm⟩⟩
    ac_rfl
  have h := congrArg (fun x : torusGroup .E6 L => (x : ModGL .E6 L)) hNfix
  rw [hφ_apply (normFun φ S)] at h
  rw [Commute]
  calc n * normFun φ S = (n * normFun φ S * n⁻¹) * n := by group
    _ = normFun φ S * n := by rw [h]

theorem exists_torusRep_of_weyl_zpowers
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {n : ModGL .E6 L} (hnE : n ∈ E) {a : WeylGroup .E6}
    (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    (hAeq : A = Subgroup.zpowers a)
    {e' : ModGL .E6 L} (he' : e' ∈ E) :
    ∃ t' ∈ torusGroup .E6 L, ∃ m : ℤ, e' = t' * n ^ m := by
  have hnN : n ∈ monomialSubgroup .E6 L := hEM hnE
  have hρA : weylQuotientHom .E6 L ⟨e', hEM he'⟩ ∈ A :=
    (hEA _).2 ⟨e', he', rfl⟩
  rw [hAeq] at hρA
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hρA
  let t' : ModGL .E6 L := e' * (n ^ m)⁻¹
  have ht'N : t' ∈ monomialSubgroup .E6 L :=
    mul_mem (hEM he') (inv_mem (Subgroup.zpow_mem (K := monomialSubgroup .E6 L) hnN m))
  have hρt' : weylQuotientHom .E6 L ⟨t', ht'N⟩ = 1 := by
    have ht'eq : (⟨t', ht'N⟩ : monomialSubgroup .E6 L) =
        (⟨e', hEM he'⟩ : monomialSubgroup .E6 L) *
          (⟨n, hnN⟩ : monomialSubgroup .E6 L) ^ (-m) := by
      apply Subtype.ext
      change e' * (n ^ m)⁻¹ = e' * n ^ (-m)
      rw [zpow_neg]
    rw [ht'eq, map_mul, map_zpow, ← hm, hnρ]
    group
  have ht'T : t' ∈ torusGroup .E6 L := by
    have hker : (⟨t', ht'N⟩ : monomialSubgroup .E6 L) ∈ (weylQuotientHom .E6 L).ker := hρt'
    rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2,
      Subgroup.mem_subgroupOf] at hker
    exact hker
  exact ⟨t', ht'T, m, by dsimp only [t']; group⟩

private theorem normFun_commutes_E
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {n : ModGL .E6 L} (hnE : n ∈ E) {a : WeylGroup .E6}
    (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    (hAeq : A = Subgroup.zpowers a)
    (hTcomm : ∀ x y : torusGroup .E6 L, x * y = y * x)
    (S : torusGroup .E6 L) :
    ∀ e ∈ E, ((normFun (normPhi n (hEM hnE)) S : torusGroup .E6 L) : ModGL .E6 L) * e =
      e * ((normFun (normPhi n (hEM hnE)) S : torusGroup .E6 L) : ModGL .E6 L) := by
  intro e' he'
  obtain ⟨t', ht'T, m, heq⟩ :=
    exists_torusRep_of_weyl_zpowers hEM hEA hnE hnρ hAeq he'
  let N : torusGroup .E6 L := normFun (normPhi n (hEM hnE)) S
  have hcomm_n : Commute (n ^ m) N :=
    (normFun_fixed_n hEM hE hnE hTcomm S).zpow_left m
  have hcomm_t' : Commute t' (N : ModGL .E6 L) :=
    congrArg (fun x : torusGroup .E6 L => (x : ModGL .E6 L))
      (hTcomm ⟨t', ht'T⟩ ⟨N, N.2⟩)
  have hcomm_e' : Commute e' N := by
    rw [heq]
    exact hcomm_t'.mul_left hcomm_n
  exact hcomm_e'.eq.symm

theorem normFun_mem_closedIdentityComponent
    {L : Type} [Field L] [IsAlgClosed L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {n : ModGL .E6 L} (hnE : n ∈ E) {a : WeylGroup .E6}
    (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    (hAeq : A = Subgroup.zpowers a)
    (hTcomm : ∀ x y : torusGroup .E6 L, x * y = y * x)
    (S : torusGroup .E6 L) :
    ((normFun (normPhi n (hEM hnE)) S : torusGroup .E6 L) : ModGL .E6 L) ∈
      CFSG.LieType.AlgebraicGroups.closedIdentityComponent
        (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) := by
  have hT := CFSG.StandardType.F4ExplicitPos.ConnectedJoint.isConnectedAlgebraicSubgroup_torus_sup_rootSpan_no117 (τ := Tag.E6) (k := L) ∅
  have hroot : rootSpan .E6 L ∅ = ⊥ := by
    simp only [rootSpan, Set.mem_empty_iff_false, iSup_false, iSup_bot]
  rw [hroot, sup_bot_eq] at hT
  let φ := normPhi n (hEM hnE)
  have heval (s : torusGroup .E6 L) :
      ((normFun φ s : torusGroup .E6 L) : ModGL .E6 L) =
        (s : ModGL .E6 L) * (n * s * n⁻¹) * (n ^ 2 * s * (n ^ 2)⁻¹) := by
    simp only [normFun, Subgroup.coe_mul, φ, normPhi_apply]
    group
  have hm := CFSG.LieType.AlgebraicGroups.threeConjugateNorm_mem_closedIdentityComponent
    (torusGroup .E6 L) (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)))
    hT n (fun s hs => by
      let sT : torusGroup .E6 L := ⟨s,hs⟩
      change (sT : ModGL .E6 L) * (n * sT * n⁻¹) *
        (n ^ 2 * sT * (n ^ 2)⁻¹) ∈ _
      rw [← heval sT]
      refine ⟨CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup
        (normFun φ sT).property, ?_⟩
      change ((normFun φ sT : torusGroup .E6 L) : ModGL .E6 L) ∈
        Subgroup.centralizer (E : Set (ModGL .E6 L))
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (normFun_commutes_E hEM hE hEA hnE hnρ hAeq hTcomm sT e he).symm)
    S.property
  rw [← heval S] at hm
  exact hm

private theorem normFun_exists_pow_roots
    {L : Type} [Field L] [IsAlgClosed L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {n : ModGL .E6 L} (hnE : n ∈ E) {a : WeylGroup .E6}
    (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    (hAeq : A = Subgroup.zpowers a)
    (hTcomm : ∀ x y : torusGroup .E6 L, x * y = y * x)
    (S : torusGroup .E6 L) :
    ∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
      (∀ e ∈ E, c' * e = e * c') ∧
      ((normFun (normPhi n (hEM hnE)) S : torusGroup .E6 L) : ModGL .E6 L) =
        c' ^ (3 ^ m) := by
  intro m
  obtain ⟨sm, hsmT, hsm3⟩ :=
    exists_torus_pow_eq (t := (S : ModGL .E6 L)) S.2 (n := 3 ^ m)
      (pow_pos (by norm_num) m)
  let Sm : torusGroup .E6 L := ⟨sm, hsmT⟩
  have hSm : Sm ^ (3 ^ m) = S := Subtype.ext hsm3
  let c' : ModGL .E6 L := (normFun (normPhi n (hEM hnE)) Sm : torusGroup .E6 L)
  have hc'T : c' ∈ torusGroup .E6 L := (normFun (normPhi n (hEM hnE)) Sm).2
  have hc'G : c' ∈ adjointGroup .E6 L :=
    CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup hc'T
  have hc'comm : ∀ e ∈ E, c' * e = e * c' :=
    normFun_commutes_E hEM hE hEA hnE hnρ hAeq hTcomm Sm
  refine ⟨c', hc'G, hc'comm, ?_⟩
  have h1 : ((normFun (normPhi n (hEM hnE)) (Sm ^ (3 ^ m)) :
      torusGroup .E6 L) : ModGL .E6 L) =
      (((normFun (normPhi n (hEM hnE)) Sm) ^ (3 ^ m) : torusGroup .E6 L) :
        ModGL .E6 L) :=
    congrArg (fun x : torusGroup .E6 L => (x : ModGL .E6 L))
      (normFun_pow (normPhi n (hEM hnE)) hTcomm (3 ^ m) Sm)
  calc ((normFun (normPhi n (hEM hnE)) S : torusGroup .E6 L) : ModGL .E6 L) =
      ((normFun (normPhi n (hEM hnE)) (Sm ^ (3 ^ m)) :
        torusGroup .E6 L) : ModGL .E6 L) := by rw [hSm]
    _ = c' ^ (3 ^ m) := h1

private theorem normFun_eq_cube_of_fixed
    {L : Type} [Field L]
    {φ : torusGroup .E6 L →* torusGroup .E6 L}
    {X : torusGroup .E6 L} (hφX : φ X = X) :
    normFun φ X = X ^ 3 := by
  rw [normFun, hφX, hφX]
  apply Subtype.ext
  simp [pow_succ, mul_assoc]

private theorem normDescent_cube
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) {n : ModGL .E6 L} (hnE : n ∈ E)
    {t : ModGL .E6 L} (ht : t ∈ torusGroup .E6 L)
    (htE : ∀ e ∈ E, t * e = e * t)
    {s : ModGL .E6 L} (hsT : s ∈ torusGroup .E6 L) (hs3 : s ^ 3 = t) :
    ((normFun (normPhi n (hEM hnE)) ⟨s, hsT⟩ : torusGroup .E6 L) :
        ModGL .E6 L) ^ 3 = t ^ 3 := by
  have hTcomm : ∀ x y : torusGroup .E6 L, x * y = y * x := torusGroup_comm
  let φ : torusGroup .E6 L →* torusGroup .E6 L := normPhi n (hEM hnE)
  let S : torusGroup .E6 L := ⟨s, hsT⟩
  let dT : torusGroup .E6 L := normFun φ S
  have hφt : φ ⟨t, ht⟩ = ⟨t, ht⟩ := by
    apply Subtype.ext
    change ((normPhi n (hEM hnE) ⟨t, ht⟩ : torusGroup .E6 L) : ModGL .E6 L) = t
    rw [normPhi_apply]
    calc n * t * n⁻¹ = (t * n) * n⁻¹ := by rw [show n * t = t * n from (htE n hnE).symm]
      _ = t := by group
  have hNt : normFun φ ⟨t, ht⟩ = ⟨t, ht⟩ ^ 3 :=
    normFun_eq_cube_of_fixed hφt
  have hpow : (dT ^ 3 : torusGroup .E6 L) = normFun φ (S ^ 3) :=
    (normFun_pow φ hTcomm 3 S).symm
  have hS3 : S ^ 3 = ⟨t, ht⟩ := Subtype.ext hs3
  calc ((dT : torusGroup .E6 L) : ModGL .E6 L) ^ 3 =
      ((dT ^ 3 : torusGroup .E6 L) : ModGL .E6 L) := by simp
    _ = ((normFun φ (S ^ 3) : torusGroup .E6 L) : ModGL .E6 L) := by rw [hpow]
    _ = ((normFun φ ⟨t, ht⟩ : torusGroup .E6 L) : ModGL .E6 L) := by rw [hS3]
    _ = t ^ 3 := by rw [hNt]; rfl

private theorem normDescent_e_mem
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {a : WeylGroup .E6} (hAeq : A = Subgroup.zpowers a)
    {n : ModGL .E6 L} (hnE : n ∈ E)
    (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    {t : ModGL .E6 L} (ht : t ∈ torusGroup .E6 L)
    (htE : ∀ e ∈ E, t * e = e * t)
    {S : torusGroup .E6 L}
    (hd3 : ((normFun (normPhi n (hEM hnE)) S : torusGroup .E6 L) :
        ModGL .E6 L) ^ 3 = t ^ 3) :
    t * ((normFun (normPhi n (hEM hnE)) S : torusGroup .E6 L) :
      ModGL .E6 L)⁻¹ ∈ E := by
  have hTcomm : ∀ x y : torusGroup .E6 L, x * y = y * x := torusGroup_comm
  let φ : torusGroup .E6 L →* torusGroup .E6 L := normPhi n (hEM hnE)
  let dT : torusGroup .E6 L := normFun φ S
  let d : ModGL .E6 L := dT
  let e : ModGL .E6 L := t * d⁻¹
  have hcomm_td : Commute t d :=
    congrArg (fun x : torusGroup .E6 L => (x : ModGL .E6 L))
      (hTcomm ⟨t, ht⟩ dT)
  have he3 : e ^ 3 = 1 := by
    have hcomm' : Commute t d⁻¹ := (Commute.inv_right_iff).mpr hcomm_td
    calc e ^ 3 = t ^ 3 * (d⁻¹) ^ 3 := by
          dsimp only [e]
          rw [hcomm'.mul_pow]
      _ = t ^ 3 * (d ^ 3)⁻¹ := by rw [inv_pow]
      _ = 1 := by rw [hd3, mul_inv_cancel]
  have heT : e ∈ torusGroup .E6 L := mul_mem ht (inv_mem dT.2)
  have he_comm : ∀ e' ∈ E, e * e' = e' * e := by
    intro e' he'
    have ht_comm : Commute t e' := htE e' he'
    have hd_comm : Commute d e' :=
      normFun_commutes_E hEM hE hEA hnE hnρ hAeq hTcomm S e' he'
    have hd_inv : Commute d⁻¹ e' :=
      ((Commute.inv_right_iff).mpr hd_comm.symm).symm
    have h : Commute (t * d⁻¹) e' := ht_comm.mul_left hd_inv
    simpa [e] using h.eq
  exact mem_of_torus_of_commute hL hEM hE hcard hET hAS hAg heT he_comm he3

private theorem exists_norm_descent
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {a : WeylGroup .E6} (hAeq : A = Subgroup.zpowers a)
    {n : ModGL .E6 L} (hnE : n ∈ E)
    (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    {t : ModGL .E6 L} (ht : t ∈ torusGroup .E6 L)
    (htE : ∀ e ∈ E, t * e = e * t) :
    ∃ e ∈ E, ∃ d : ModGL .E6 L,
      (∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
        (∀ e' ∈ E, c' * e' = e' * c') ∧ d = c' ^ (3 ^ m)) ∧
      t = e * d ∧
      d ∈ CFSG.LieType.AlgebraicGroups.closedIdentityComponent
        (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) := by
  classical
  have hTcomm : ∀ x y : torusGroup .E6 L, x * y = y * x := torusGroup_comm
  let φ : torusGroup .E6 L →* torusGroup .E6 L := normPhi n (hEM hnE)
  obtain ⟨s, hsT, hs3⟩ := exists_torus_pow_eq ht (n := 3) (by norm_num)
  let S : torusGroup .E6 L := ⟨s, hsT⟩
  let dT : torusGroup .E6 L := normFun φ S
  let d : ModGL .E6 L := dT
  let e : ModGL .E6 L := t * d⁻¹
  have hd3 : d ^ 3 = t ^ 3 := normDescent_cube hEM hnE ht htE hsT hs3
  have heE : e ∈ E := normDescent_e_mem hL hEM hE hcard hET hAS hAg hEA hAeq hnE hnρ
    ht htE (S := S) hd3
  refine ⟨e, heE, d, ?_, ⟨?_, ?_⟩⟩
  · simpa [d, dT, φ] using
      normFun_exists_pow_roots hEM hE hEA hnE hnρ hAeq hTcomm S
  · dsimp [e]
    group
  · exact normFun_mem_closedIdentityComponent hEM hE hEA hnE hnρ hAeq hTcomm S

private def weylImage
    {L : Type} [Field L] (E : Subgroup (ModGL .E6 L)) : Subgroup (WeylGroup .E6) :=
  (E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L)

private theorem weylImage_mem_iff
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) {w : WeylGroup .E6} :
    w ∈ weylImage E ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w := by
  constructor
  · intro hw
    rw [weylImage, Subgroup.mem_map] at hw
    obtain ⟨e, he, hwe⟩ := hw
    rw [Subgroup.mem_subgroupOf] at he
    exact ⟨e, he, hwe⟩
  · rintro ⟨e, he, rfl⟩
    refine Subgroup.mem_map.2 ⟨⟨e, hEM he⟩, ?_, rfl⟩
    rwa [Subgroup.mem_subgroupOf]

private theorem weylImage_le_range
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range) :
    weylImage E ≤ modelHomE6.range := by
  rintro w hw
  obtain ⟨e, he, rfl⟩ := (weylImage_mem_iff hEM).1 hw
  exact hAS e he

private theorem weylImage_isElemAbelian
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E) :
    IsElemAbelian 3 (weylImage E) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e, he, hae⟩ := (weylImage_mem_iff hEM).1 x.2
    obtain ⟨e', he', hbe⟩ := (weylImage_mem_iff hEM).1 y.2
    have hcomm : e * e' = e' * e := hE.comm he he'
    change (x : WeylGroup .E6) * y = (y : WeylGroup .E6) * x
    rw [← hae, ← hbe, ← map_mul, ← map_mul]
    exact congrArg (weylQuotientHom .E6 L) (Subtype.ext hcomm)
  · obtain ⟨e, he, hxe⟩ := (weylImage_mem_iff hEM).1 hx
    have h3 : (⟨e, hEM he⟩ : monomialSubgroup .E6 L) ^ 3 = 1 :=
      Subtype.ext (hE.2 e he)
    calc x ^ 3 = (weylQuotientHom .E6 L ⟨e, hEM he⟩) ^ 3 := by rw [← hxe]
      _ = weylQuotientHom .E6 L ((⟨e, hEM he⟩ : monomialSubgroup .E6 L) ^ 3) :=
          (map_pow (weylQuotientHom .E6 L) ⟨e, hEM he⟩ 3).symm
      _ = weylQuotientHom .E6 L 1 := by rw [h3]
      _ = 1 := map_one _

private theorem weylImage_ne_bot
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hET : ¬ E ≤ torusGroup .E6 L) :
    weylImage E ≠ ⊥ := by
  intro hbot
  apply hET
  intro e he
  have hmem : weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ weylImage E :=
    (weylImage_mem_iff hEM).2 ⟨e, he, rfl⟩
  rw [hbot] at hmem
  have h1 : weylQuotientHom .E6 L ⟨e, hEM he⟩ = 1 := Subgroup.mem_bot.1 hmem
  have hker : (⟨e, hEM he⟩ : monomialSubgroup .E6 L) ∈
      (weylQuotientHom .E6 L).ker := h1
  rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2,
    Subgroup.mem_subgroupOf] at hker
  exact hker

private theorem weylImage_ne_zpowers_gE6
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i) :
    ∀ i, weylImage E ≠ Subgroup.zpowers (gE6 i) := by
  intro i hAeq
  have hmem : gE6 i ∈ weylImage E := by
    rw [hAeq]
    exact Subgroup.mem_zpowers _
  obtain ⟨e, he, hρ⟩ := (weylImage_mem_iff hEM).1 hmem
  exact hAg e he i hρ

private theorem weylGenerator_avoids_inverses
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {A : Subgroup (WeylGroup .E6)} {a : WeylGroup .E6} {n : ModGL .E6 L}
    (hnE : n ∈ E) (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    (hAeq : A = Subgroup.zpowers a) (hAcard : Nat.card A = 3)
    (ha3 : a ^ 3 = 1)
    (hAgA : ∀ i, A ≠ Subgroup.zpowers (gE6 i)) :
    (∀ i, a ≠ gE6 i) ∧ (∀ i, a ≠ (gE6 i)⁻¹) := by
  have hn2 : a ^ 2 = a⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc a ^ 2 * a = a ^ (2 + 1) := (pow_succ a 2).symm
      _ = a ^ 3 := by norm_num
      _ = 1 := ha3
  constructor
  · intro i hg
    exact hAg n hnE i (hnρ.trans hg)
  · intro i hginv
    have hmem : gE6 i ∈ A := by
      have hginv' : a⁻¹ = gE6 i := by rw [hginv, inv_inv]
      have h2 : gE6 i = a ^ 2 := hginv'.symm.trans hn2.symm
      rw [hAeq, h2]
      exact Subgroup.zpow_mem_zpowers a 2
    have hcardg : Nat.card (Subgroup.zpowers (gE6 i)) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (p := 3) (gE6_pow_three i)]
      intro h1
      exact hAg n hnE i (by rw [hnρ, hginv, h1, inv_one])
    have hle : Subgroup.zpowers (gE6 i) ≤ A := Subgroup.zpowers_le.2 hmem
    exact hAgA i (Subgroup.eq_of_le_of_card_ge hle (by rw [hAcard, hcardg])).symm

private theorem weylGenerator_exists
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    (hAcard : Nat.card A = 3) (hAne : A ≠ ⊥) (hA : IsElemAbelian 3 A)
    (hAgA : ∀ i, A ≠ Subgroup.zpowers (gE6 i)) :
    ∃ (n : ModGL .E6 L), ∃ hnE : n ∈ E, ∃ (a : WeylGroup .E6),
      weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a ∧ A = Subgroup.zpowers a ∧
      a ^ 3 = 1 ∧ a ≠ 1 ∧ (∀ i, a ≠ gE6 i) ∧ (∀ i, a ≠ (gE6 i)⁻¹) := by
  obtain ⟨aA, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
  let a : WeylGroup .E6 := aA
  have haA : a ∈ A := aA.2
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hgen : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.2 haA
  have hcardz : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 3) ha3 (by simpa [a] using ha1)]
  have hAeq : A = Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge hgen (by rw [hAcard, hcardz])).symm
  obtain ⟨n, hnE, hnρ⟩ := (hEA a).1 haA
  obtain ⟨hag, hagi⟩ := weylGenerator_avoids_inverses hEM hAg hnE hnρ hAeq hAcard ha3 hAgA
  exact ⟨n, hnE, a, hnρ, hAeq, ha3, by simpa [a] using ha1, hag, hagi⟩

theorem exists_weylGenerator
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    (hA3 : Nat.card ((E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L)) = 3) :
    ∃ (A : Subgroup (WeylGroup .E6)),
      Nat.card A = 3 ∧
      (∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E, weylQuotientHom .E6 L ⟨e, hEM he⟩ = w) ∧
      A ≤ modelHomE6.range ∧ IsElemAbelian 3 A ∧ A ≠ ⊥ ∧
      (∀ i, A ≠ Subgroup.zpowers (gE6 i)) ∧
      ∃ (n : ModGL .E6 L), ∃ hnE : n ∈ E, ∃ (a : WeylGroup .E6),
        weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a ∧ A = Subgroup.zpowers a ∧
        a ^ 3 = 1 ∧ a ≠ 1 ∧ (∀ i, a ≠ gE6 i) ∧ (∀ i, a ≠ (gE6 i)⁻¹) := by
  let A : Subgroup (WeylGroup .E6) := weylImage E
  have hAcard : Nat.card A = 3 := hA3
  have hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w := fun w => weylImage_mem_iff hEM
  have hAS' : A ≤ modelHomE6.range := weylImage_le_range hEM hAS
  have hA : IsElemAbelian 3 A := weylImage_isElemAbelian hEM hE
  have hAne : A ≠ ⊥ := weylImage_ne_bot hEM hET
  have hAgA : ∀ i, A ≠ Subgroup.zpowers (gE6 i) := weylImage_ne_zpowers_gE6 hEM hAg
  obtain ⟨n, hnE, a, hnρ, hAeq, ha3, ha1, hag, hagi⟩ :=
    weylGenerator_exists hEM hAg hEA hAcard hAne hA hAgA
  exact ⟨A, hAcard, hEA, hAS', hA, hAne, hAgA, n, hnE, a, hnρ, hAeq, ha3, ha1, hag, hagi⟩

theorem exists_mul_pow_of_torus
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    (hA3 : Nat.card ((E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L)) = 3)
    {t : ModGL .E6 L} (ht : t ∈ torusGroup .E6 L) (htE : ∀ e ∈ E, t * e = e * t) :
    ∃ e ∈ E, ∃ d : ModGL .E6 L, (∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
      (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ t = e * d := by
  obtain ⟨A, -, hEA, -, -, -, -, n, hnE, a, hnρ, hAeq, -⟩ :=
    exists_weylGenerator hEM hE hET hAS hAg hA3
  obtain ⟨e, he, d, hd, htd, -⟩ :=
    exists_norm_descent hL hEM hE hcard hET hAS hAg hEA hAeq hnE hnρ ht htE
  exact ⟨e, he, d, hd, htd⟩

theorem exists_mul_connected_of_torus
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    (hA3 : Nat.card ((E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L)) = 3)
    {t : ModGL .E6 L} (ht : t ∈ torusGroup .E6 L) (htE : ∀ e ∈ E, t * e = e * t) :
    ∃ e ∈ E, ∃ d ∈ CFSG.LieType.AlgebraicGroups.closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))), t = e * d := by
  obtain ⟨A, -, hEA, -, -, -, -, n, hnE, a, hnρ, hAeq, -⟩ :=
    exists_weylGenerator hEM hE hET hAS hAg hA3
  obtain ⟨e, he, d, -, htd, hd⟩ :=
    exists_norm_descent hL hEM hE hcard hET hAS hAg hEA hAeq hnE hnρ ht htE
  exact ⟨e, he, d, hd, htd⟩

private abbrev ModelKey := (Fin 3 → ZMod 3) × ZMod 3

private def singleCoord (i : Fin 3) (c : ZMod 3) : Fin 3 → ZMod 3 := Pi.single i c

private abbrev FormData := (Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ZMod 3)

private def modelVec (v : Fin 3 → ZMod 3) (m : ZMod 3) : Model piE7 piE7_pow_three :=
  ⟨Multiplicative.ofAdd v, Multiplicative.ofAdd m⟩

private def modelWord (v : Fin 3 → ZMod 3) (m : ZMod 3) : List (Fin Tag.E6.rank) :=
  nfWordE6 (v 0).val (v 1).val (v 2).val ++ (List.replicate m.val wordE6C).flatten

private def modelWordAct (p : ModelKey) (x : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  (modelWord p.1 p.2).foldr (reflect .E6) x

private def formTable : List (ModelKey × FormData) := [
  ((![0,0,0], 1), (![-1,-1,-1,-1,0,0], ![0,0,0,1,0,0])),
  ((![0,0,0], 2), (![-1,-1,-1,-1,0,0], ![0,0,0,1,0,0])),
  ((![0,1,1], 0), (![0,-1,0,0,-1,-1], ![0,1,0,0,2,2])),
  ((![0,1,2], 0), (![0,-1,0,0,-1,0], ![0,1,0,0,1,1])),
  ((![0,1,2], 1), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![0,1,2], 2), (![-1,-1,-1,-1,-1,0], ![0,0,0,1,0,0])),
  ((![0,2,1], 0), (![0,-1,0,0,-1,0], ![0,1,0,0,1,1])),
  ((![0,2,1], 1), (![-1,-1,-1,-1,-1,0], ![0,0,0,1,0,0])),
  ((![0,2,1], 2), (![-1,-1,-1,-1,0,1], ![0,0,0,1,0,0])),
  ((![0,2,2], 0), (![0,-1,0,0,-1,-1], ![0,1,0,0,2,2])),
  ((![1,0,1], 0), (![-1,-1,-1,0,0,0], ![1,2,1,0,0,0])),
  ((![1,0,2], 0), (![-1,-1,0,0,0,0], ![1,1,1,0,0,0])),
  ((![1,0,2], 1), (![-1,-1,-1,-1,-1,0], ![0,0,0,1,0,0])),
  ((![1,0,2], 2), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![1,1,0], 0), (![-1,0,-1,0,-1,0], ![1,0,1,0,2,2])),
  ((![1,1,1], 0), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![1,1,1], 1), (![-1,-1,-1,-1,0,0], ![0,0,0,1,0,0])),
  ((![1,1,1], 2), (![-1,0,-1,-1,-1,0], ![0,0,0,1,0,0])),
  ((![1,1,2], 0), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![1,2,0], 0), (![-1,0,-1,0,-1,-1], ![1,0,1,0,1,1])),
  ((![1,2,0], 1), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![1,2,0], 2), (![-1,-1,-1,-1,-1,0], ![0,0,0,1,0,0])),
  ((![1,2,1], 0), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![1,2,2], 0), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![2,0,1], 0), (![-1,-1,0,0,0,0], ![1,1,1,0,0,0])),
  ((![2,0,1], 1), (![-1,-1,-1,-1,0,1], ![0,0,0,1,0,0])),
  ((![2,0,1], 2), (![-1,-1,-1,-1,0,-1], ![0,0,0,1,0,0])),
  ((![2,0,2], 0), (![-1,-1,-1,0,0,0], ![1,2,1,0,0,0])),
  ((![2,1,0], 0), (![-1,0,-1,0,-1,-1], ![1,0,1,0,1,1])),
  ((![2,1,0], 1), (![-1,-1,-1,-1,0,-1], ![0,0,0,1,0,0])),
  ((![2,1,0], 2), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![2,1,1], 0), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![2,1,2], 0), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![2,2,0], 0), (![-1,0,-1,0,-1,0], ![1,0,1,0,2,2])),
  ((![2,2,1], 0), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![2,2,2], 0), (![-1,-1,-1,-1,-1,-1], ![0,0,0,1,0,0])),
  ((![2,2,2], 1), (![-1,0,-1,-1,-1,0], ![0,0,0,1,0,0])),
  ((![2,2,2], 2), (![-1,-1,-1,-1,0,0], ![0,0,0,1,0,0]))]

private def formTableKeys : List ModelKey := formTable.map Prod.fst

private def formDataOf (p : ModelKey) : FormData :=
  ((formTable.find? fun e => e.1 = p).map Prod.snd).getD
    ((0 : Fin Tag.E6.rank → ℤ), (0 : Fin Tag.E6.rank → ZMod 3))

private def formRoot (p : ModelKey) : Fin Tag.E6.rank → ℤ := (formDataOf p).1

private def formFixed (p : ModelKey) : Fin Tag.E6.rank → ZMod 3 := (formDataOf p).2

private def zmod3Eq (a b : ZMod 3) : Bool := a.val == b.val

private theorem zmod3Eq_eq_true {a b : ZMod 3} : zmod3Eq a b = true ↔ a = b := by
  unfold zmod3Eq
  rw [beq_iff_eq]
  exact ⟨fun h => ZMod.val_injective 3 h, congrArg ZMod.val⟩

private def vec3Eq {n : ℕ} (x y : Fin n → ZMod 3) : Bool :=
  (List.finRange n).all fun i => zmod3Eq (x i) (y i)

private theorem vec3Eq_eq_true {n : ℕ} {x y : Fin n → ZMod 3} :
    vec3Eq x y = true ↔ x = y := by
  unfold vec3Eq
  rw [List.all_eq_true]
  constructor
  · intro h
    funext i
    exact zmod3Eq_eq_true.mp (h i (List.mem_finRange i))
  · intro h
    intro i _
    rw [h]
    exact zmod3Eq_eq_true.mpr rfl

private def vecIntEq {n : ℕ} (x y : Fin n → ℤ) : Bool :=
  (List.finRange n).all fun i => decide (x i = y i)

private theorem vecIntEq_eq_true {n : ℕ} {x y : Fin n → ℤ} :
    vecIntEq x y = true ↔ x = y := by
  unfold vecIntEq
  rw [List.all_eq_true]
  constructor
  · intro h
    funext i
    exact of_decide_eq_true (h i (List.mem_finRange i))
  · intro h
    intro i _
    rw [h]
    exact decide_eq_true rfl

private def formEntryCheck (p : ModelKey) : Bool :=
  vecIntEq (formRoot p + modelWordAct p (formRoot p) +
    modelWordAct p (modelWordAct p (formRoot p))) 0 &&
  vec3Eq (adWord .E6 3 (modelWord p.1 p.2) (formFixed p)) (formFixed p) &&
  decide ((∑ i, ((formRoot p i : ZMod 3) * formFixed p i)) ≠ 0)

private theorem formTable_good :
    formTable.all (fun e => formEntryCheck e.1) = true := by
  decide +kernel

private theorem formEntry_of_mem_table (p : ModelKey) (hp : p ∈ formTableKeys) :
    formRoot p + modelWordAct p (formRoot p) + modelWordAct p (modelWordAct p (formRoot p)) = 0 ∧
    adWord .E6 3 (modelWord p.1 p.2) (formFixed p) = formFixed p ∧
    (∑ i, ((formRoot p i : ZMod 3) * formFixed p i)) ≠ 0 := by
  have h := List.all_eq_true.mp formTable_good
  rcases List.mem_map.mp hp with ⟨e, he, hpe⟩
  rw [← hpe]
  have hh := h e he
  simp only [formEntryCheck, Bool.and_eq_true] at hh
  refine ⟨vecIntEq_eq_true.mp hh.1.1, vec3Eq_eq_true.mp hh.1.2, ?_⟩
  exact of_decide_eq_true hh.2

private def modelKeyEq (p q : ModelKey) : Bool :=
  vec3Eq p.1 q.1 && zmod3Eq p.2 q.2

private theorem modelKeyEq_eq_true {p q : ModelKey} : modelKeyEq p q = true ↔ p = q := by
  unfold modelKeyEq
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact Prod.ext (vec3Eq_eq_true.mp h1) (zmod3Eq_eq_true.mp h2)
  · intro h
    subst h
    exact ⟨vec3Eq_eq_true.mpr rfl, zmod3Eq_eq_true.mpr rfl⟩

private def IsExcludedKey (p : ModelKey) : Prop :=
  (∃ i : Fin 3, p = (singleCoord i 1, 0)) ∨
  (∃ i : Fin 3, p = (singleCoord i 2, 0))

private def excludedKeyCheck (p : ModelKey) : Bool :=
  (List.finRange 3).any (fun i => modelKeyEq p (singleCoord i 1, 0)) ||
  (List.finRange 3).any (fun i => modelKeyEq p (singleCoord i 2, 0))

private theorem excludedKeyCheck_eq_true {p : ModelKey} :
    excludedKeyCheck p = true ↔ IsExcludedKey p := by
  unfold excludedKeyCheck IsExcludedKey
  rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro (⟨i, -, hi⟩ | ⟨i, -, hi⟩)
    · exact Or.inl ⟨i, modelKeyEq_eq_true.mp hi⟩
    · exact Or.inr ⟨i, modelKeyEq_eq_true.mp hi⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inl ⟨i, List.mem_finRange i, modelKeyEq_eq_true.mpr rfl⟩
    · exact Or.inr ⟨i, List.mem_finRange i, modelKeyEq_eq_true.mpr rfl⟩

private def modelKeyNotZero (p : ModelKey) : Bool := !modelKeyEq p 0

private def modelEq (y z : Model piE7 piE7_pow_three) : Bool :=
  vec3Eq y.left.toAdd z.left.toAdd && zmod3Eq y.right.toAdd z.right.toAdd

private theorem modelEq_eq_true {y z : Model piE7 piE7_pow_three} :
    modelEq y z = true ↔ y = z := by
  unfold modelEq
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    apply SemidirectProduct.ext
    · exact Multiplicative.toAdd.injective (vec3Eq_eq_true.mp h1)
    · exact Multiplicative.toAdd.injective (zmod3Eq_eq_true.mp h2)
  · intro h
    subst h
    exact ⟨vec3Eq_eq_true.mpr rfl, zmod3Eq_eq_true.mpr rfl⟩

private def modelKeyMem (p : ModelKey) : Bool :=
  formTable.any fun e => modelKeyEq e.1 p

private theorem modelKeyMem_eq_true {p : ModelKey} : modelKeyMem p = true ↔ p ∈ formTableKeys := by
  unfold modelKeyMem formTableKeys
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, hpe⟩
    exact List.mem_map.mpr ⟨e, he, modelKeyEq_eq_true.mp hpe⟩
  · intro hp
    rcases List.mem_map.mp hp with ⟨e, he, hpe⟩
    exact ⟨e, he, modelKeyEq_eq_true.mpr hpe⟩

private def coverageCheck (p : ModelKey) : Bool :=
  !(modelEq (modelVec p.1 p.2 ^ 3) 1 && modelKeyNotZero p && !excludedKeyCheck p) ||
    modelKeyMem p

private theorem coverage : ∀ p : ModelKey, coverageCheck p = true := by
  decide +kernel

private theorem formTableKeys_of_admissible (p : ModelKey)
    (h3 : modelVec p.1 p.2 ^ 3 = 1) (h1 : p ≠ 0) (hex : ¬ IsExcludedKey p) :
    p ∈ formTableKeys := by
  have hcov := coverage p
  have h3b : modelEq (modelVec p.1 p.2 ^ 3) 1 = true :=
    modelEq_eq_true.mpr h3
  have h1b : modelKeyNotZero p = true := by
    unfold modelKeyNotZero
    by_cases h : modelKeyEq p 0 = true
    · exact absurd (modelKeyEq_eq_true.mp h) h1
    · simp [h]
  have hexb : excludedKeyCheck p = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hex (excludedKeyCheck_eq_true.mp h)
  unfold coverageCheck at hcov
  rw [h3b, h1b, hexb] at hcov
  simp at hcov
  exact modelKeyMem_eq_true.mp hcov

private theorem modelHomE6_modelVec (v : Fin 3 → ZMod 3) (m : ZMod 3) :
    modelHomE6 (modelVec v m) = (coxeterSystem .E6).wordProd (modelWord v m) := by
  rw [modelVec]
  change modelHom isModel_E6 ⟨Multiplicative.ofAdd v, Multiplicative.ofAdd m⟩ =
    (coxeterSystem .E6).wordProd (modelWord v m)
  rw [TableBExc.Three.modelHom_apply]
  have hleft : (modelN isModel_E6) (Multiplicative.ofAdd v) =
      (coxeterSystem .E6).wordProd (nfWordE6 (v 0).val (v 1).val (v 2).val) := by
    rw [← TableBExc.Three.modelHom_inl (h := isModel_E6)]
    change modelHomE6 (SemidirectProduct.inl (Multiplicative.ofAdd v)) =
      (coxeterSystem .E6).wordProd (nfWordE6 (v 0).val (v 1).val (v 2).val)
    rw [modelHomE6_inl]
    rfl
  rw [hleft, modelWord, CoxeterSystem.wordProd_append]
  congr 1
  change (coxeterSystem .E6).wordProd wordE6C ^ m.val =
    (coxeterSystem .E6).wordProd (List.replicate m.val wordE6C).flatten
  rw [← CFSG.StandardType.TableBExc.wordProd_replicate]

theorem modelHomE6_inl_single_one (i : Fin 3) : modelHomE6
    (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i 1))) = gE6 i := by
  rw [modelHomE6_inl]
  congr 1
  fin_cases i <;> rfl

theorem modelHomE6_inl_single_two (i : Fin 3) : modelHomE6
    (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i 2))) = (gE6 i)⁻¹ := by
  rw [modelHomE6_inl]
  have hw : nfWordE6 ((Pi.single i (2 : ZMod 3) : Fin 3 → ZMod 3) 0).val
      ((Pi.single i (2 : ZMod 3) : Fin 3 → ZMod 3) 1).val ((Pi.single i (2 : ZMod 3) : Fin 3 → ZMod 3) 2).val =
      (List.replicate 2 (wordE6G i)).flatten := by
    fin_cases i <;> rfl
  change (coxeterSystem .E6).wordProd
    (nfWordE6 ((Pi.single i (2 : ZMod 3) : Fin 3 → ZMod 3) 0).val
      ((Pi.single i (2 : ZMod 3) : Fin 3 → ZMod 3) 1).val
      ((Pi.single i (2 : ZMod 3) : Fin 3 → ZMod 3) 2).val) = (gE6 i)⁻¹
  rw [hw,CFSG.StandardType.TableBExc.wordProd_replicate]
  change (gE6 i) ^ 2 = (gE6 i)⁻¹
  apply eq_inv_of_mul_eq_one_left
  calc (gE6 i) ^ 2 * gE6 i = (gE6 i) ^ (2 + 1) := (pow_succ (gE6 i) 2).symm
    _ = 1 := gE6_pow_three i

private theorem modelVec_toAdd (y : Model piE7 piE7_pow_three) :
    modelVec y.left.toAdd y.right.toAdd = y := by
  cases y with
  | mk l r =>
    cases l with
    | ofAdd v =>
      cases r with
      | ofAdd m => rfl

private theorem not_excludedKey_of_ne (p : ModelKey)
    (h1 : ∀ i, modelHomE6 (modelVec p.1 p.2) ≠ gE6 i)
    (h2 : ∀ i, modelHomE6 (modelVec p.1 p.2) ≠ (gE6 i)⁻¹) :
    ¬ IsExcludedKey p := by
  rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact h1 i (by
      rw [show modelVec (singleCoord i 1) 0 =
        SemidirectProduct.inl (Multiplicative.ofAdd (singleCoord i 1)) from rfl]
      exact modelHomE6_inl_single_one i)
  · exact h2 i (by
      rw [show modelVec (singleCoord i 2) 0 =
        SemidirectProduct.inl (Multiplicative.ofAdd (singleCoord i 2)) from rfl]
      exact modelHomE6_inl_single_two i)

private theorem modelData_exists (y : Model piE7 piE7_pow_three)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hyg : ∀ i, modelHomE6 y ≠ gE6 i)
    (hygi : ∀ i, modelHomE6 y ≠ (gE6 i)⁻¹) :
    ∃ β : Fin Tag.E6.rank → ℤ, ∃ x0 : Fin Tag.E6.rank → ZMod 3,
      β + modelHomE6 y • β + modelHomE6 y • (modelHomE6 y • β) = 0 ∧
      adAct .E6 3 (modelHomE6 y) x0 = x0 ∧
      (∑ i, ((β i : ZMod 3) * x0 i)) ≠ 0 := by
  let p : ModelKey := (y.left.toAdd, y.right.toAdd)
  have hvec : modelVec p.1 p.2 = y := modelVec_toAdd y
  have hp3 : modelVec p.1 p.2 ^ 3 = 1 := by rw [hvec]; exact hy3
  have hp1 : p ≠ 0 := by
    intro h
    apply hy1
    rw [← hvec, h]
    rfl
  have hpex : ¬ IsExcludedKey p :=
    not_excludedKey_of_ne p (fun i => by rw [hvec]; exact hyg i)
      (fun i => by rw [hvec]; exact hygi i)
  have hp : p ∈ formTableKeys := formTableKeys_of_admissible p hp3 hp1 hpex
  have hg := formEntry_of_mem_table p hp
  have hword : modelHomE6 (modelVec p.1 p.2) =
      (coxeterSystem .E6).wordProd (modelWord p.1 p.2) := modelHomE6_modelVec p.1 p.2
  have hb1 : modelHomE6 (modelVec p.1 p.2) • formRoot p = modelWordAct p (formRoot p) := by
    rw [hword, CFSG.StandardType.TableBExc.wordProd_smul]
    rfl
  have hb2 : modelHomE6 (modelVec p.1 p.2) •
      (modelHomE6 (modelVec p.1 p.2) • formRoot p) =
      modelWordAct p (modelWordAct p (formRoot p)) := by
    rw [hb1, hword, CFSG.StandardType.TableBExc.wordProd_smul]
    rfl
  have ha : adAct .E6 3 (modelHomE6 (modelVec p.1 p.2)) (formFixed p) =
      adWord .E6 3 (modelWord p.1 p.2) (formFixed p) := by
    rw [hword, ← adWord_eq_adAct]
  refine ⟨formRoot p, formFixed p, ?_, ?_, hg.2.2⟩
  · rw [← hvec, hb2, hb1]
    exact hg.1
  · rw [← hvec, ha]
    exact hg.2.1

private theorem adAct_eq_of_mem_E
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {d : ModGL .E6 L} (hdE : d ∈ E)
    {u : Fin Tag.E6.rank → Lˣ} (hu : d = rootDiagUnit .E6 u)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : zetaVec ζ hζ x = u) :
    ∀ a ∈ A, adAct .E6 3 a x = x := by
  intro a ha
  obtain ⟨e, he, hρe⟩ := (hEA a).1 ha
  have hconj : e * rootDiagUnit .E6 u * e⁻¹ = rootDiagUnit .E6 u := by
    rw [← hu]
    calc e * d * e⁻¹ = d * e * e⁻¹ := by rw [hE.comm he hdE]
      _ = d := by group
  have h1 := monomial_conj_rootDiagUnit_weylTuple (hEM he)
    (mapsRootLines_weylQuotientHom ⟨e, hEM he⟩) u
  have h2 : weylTuple (weylQuotientHom .E6 L ⟨e, hEM he⟩) u = u :=
    rootDiagUnit_injective (h1.symm.trans hconj)
  rw [hρe] at h2
  have h3 : weylTuple a (zetaVec ζ hζ x) = zetaVec ζ hζ x := by
    rw [hx, h2]
  have h4 : zetaVec ζ hζ (adAct .E6 3 a x) = zetaVec ζ hζ x := by
    rw [← weylTuple_zetaVec ζ hζ]
    exact h3
  exact zetaVec_injective hζo hζ h4

private theorem rootChar_fixed_of_weylTuple {L : Type} [Field L] {a : WeylGroup .E6}
    {u : Fin Tag.E6.rank → Lˣ} (hweyl : weylTuple a u = u) :
    ∀ lam : Fin Tag.E6.rank → ℤ, rootChar u (a • lam) = rootChar u lam := by
  intro lam
  calc rootChar u (a • lam) = rootChar (weylTuple a u) (a • lam) := by rw [hweyl]
    _ = rootChar u (a⁻¹ • (a • lam)) := rootChar_weylTuple a u (a • lam)
    _ = rootChar u lam := by rw [inv_smul_smul]

private theorem rootChar_three_smul_eq_one {L : Type} [Field L] {a : WeylGroup .E6}
    {u : Fin Tag.E6.rank → Lˣ} {β : Fin Tag.E6.rank → ℤ}
    (hβ : β + a • β + a • (a • β) = 0)
    (hrootfix : ∀ lam : Fin Tag.E6.rank → ℤ, rootChar u (a • lam) = rootChar u lam) :
    rootChar u ((3 : ℤ) • β) = 1 := by
  rw [rootChar_zsmul, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
  have h := congrArg (rootChar u) hβ
  rw [rootChar_add, rootChar_add, rootChar_zero] at h
  have h2 : rootChar u (a • (a • β)) = rootChar u β :=
    (hrootfix (a • β)).trans (hrootfix β)
  rw [hrootfix β, h2] at h
  simpa [pow_three, mul_assoc] using h

private theorem rootChar_three_smul_eq_zeta {L : Type} [Field L]
    {ζ : Lˣ} (hζ : ζ ^ 3 = 1) {u : Fin Tag.E6.rank → Lˣ}
    {x : Fin Tag.E6.rank → ZMod 3} {β : Fin Tag.E6.rank → ℤ}
    (hu3 : u ^ 3 = zetaVec ζ hζ x) :
    rootChar u ((3 : ℤ) • β) = rootChar (zetaVec ζ hζ x) β := by
  rw [rootChar_zsmul, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
  rw [← rootChar_pow u 3 β, hu3]

private theorem form_eq_zero_of_torus_root
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    {n : ModGL .E6 L} (hnE : n ∈ E)
    {a : WeylGroup .E6} (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {β : Fin Tag.E6.rank → ℤ}
    (hβ : β + a • β + a • (a • β) = 0)
    {t : ModGL .E6 L} (htE : ∀ e ∈ E, t * e = e * t)
    {u : Fin Tag.E6.rank → Lˣ} (hu : t = rootDiagUnit .E6 u)
    {x : Fin Tag.E6.rank → ZMod 3} (hu3 : u ^ 3 = zetaVec ζ hζ x) :
    (∑ i, ((β i : ZMod 3) * x i)) = 0 := by
  have hnN : n ∈ monomialSubgroup .E6 L := hEM hnE
  have htn : n * t * n⁻¹ = t := by
    calc n * t * n⁻¹ = t * n * n⁻¹ := by rw [htE n hnE]
      _ = t := by group
  have hconj : n * rootDiagUnit .E6 u * n⁻¹ = rootDiagUnit .E6 u := by
    rw [← hu]
    exact htn
  have h1 := monomial_conj_rootDiagUnit_weylTuple hnN
    (mapsRootLines_weylQuotientHom ⟨n, hnN⟩) u
  rw [hnρ] at h1
  have hweyl : weylTuple a u = u :=
    rootDiagUnit_injective (h1.symm.trans hconj)
  have hroot1 : rootChar u ((3 : ℤ) • β) = 1 :=
    rootChar_three_smul_eq_one hβ (rootChar_fixed_of_weylTuple hweyl)
  have hroot2 : rootChar u ((3 : ℤ) • β) = rootChar (zetaVec ζ hζ x) β :=
    rootChar_three_smul_eq_zeta hζ hu3
  have hfinal : rootChar (zetaVec ζ hζ x) β = 1 := by
    rw [← hroot2]
    exact hroot1
  have h1z : CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
      (Multiplicative.ofAdd (∑ i, ((β i : ZMod 3) * x i))) = 1 := by
    rw [← CFSG.StandardType.NoOffE8Five.rootChar_zetaVec hζ x β]
    exact hfinal
  have h2z : Multiplicative.ofAdd (∑ i, ((β i : ZMod 3) * x i)) = 1 :=
    CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ
      (h1z.trans (map_one _).symm)
  simpa using congrArg Multiplicative.toAdd h2z

private theorem exists_cube_root_of_power
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {d : ModGL .E6 L}
    (hdAll : ∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
      (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ (3 ^ m))
    (hd3 : d ^ 3 = 1) :
    ∃ t ∈ torusGroup .E6 L, (∀ e ∈ E, t * e = e * t) ∧ d = t ^ 3 ∧ d ∈ E := by
  obtain ⟨c', hc'G, hc'comm, hc'eq⟩ := hdAll 1
  obtain ⟨e, he, t, htT, htcomm, hc'⟩ :=
    exists_mul_torus_of_commute hL hEM hE hcard hET hAS hAg hc'G hc'comm
  have hdt : d = t ^ 3 := by
    have he3 : e ^ 3 = 1 := hE.2 e he
    have hcomm : Commute e t := (htcomm e he).symm
    calc d = c' ^ 3 := hc'eq
      _ = (e * t) ^ 3 := by rw [hc']
      _ = e ^ 3 * t ^ 3 := hcomm.mul_pow 3
      _ = t ^ 3 := by rw [he3, one_mul]
  have hdT : d ∈ torusGroup .E6 L := by
    rw [hdt]
    exact pow_mem htT 3
  have hdComm : ∀ e' ∈ E, d * e' = e' * d := by
    intro e' he'
    rw [hdt, pow_three]
    exact (Commute.pow_left (htcomm e' he') 3).eq
  exact ⟨t, htT, htcomm, hdt,
    mem_of_torus_of_commute hL hEM hE hcard hET hAS hAg hdT hdComm hd3⟩

private theorem exists_fixed_rootDiag
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {d : ModGL .E6 L} (hdE : d ∈ E) (hdT : d ∈ torusGroup .E6 L) :
    ∃ x : Fin Tag.E6.rank → ZMod 3,
      (∀ a' ∈ A, adAct .E6 3 a' x = x) ∧
      d = rootDiagUnit .E6 (zetaVec ζ hζ x) := by
  obtain ⟨u, hu⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdT
  have hu3 : u ^ 3 = 1 := by
    apply rootDiagUnit_injective (τ := .E6) (K := L)
    calc rootDiagUnit .E6 (u ^ 3) = rootDiagUnit .E6 u ^ 3 :=
        (rootDiagUnit_pow u 3).symm
      _ = d ^ 3 := by rw [hu]
      _ = 1 := by
        have h := hE.2 d hdE
        simpa using h
      _ = rootDiagUnit .E6 (1 : Fin Tag.E6.rank → Lˣ) := rootDiagUnit_one.symm
  obtain ⟨x, hx⟩ := exists_zetaVec_eq hζo hζ hu3
  refine ⟨x, adAct_eq_of_mem_E hEM hE hEA hζo hζ hdE hu hx, ?_⟩
  rw [hu, hx]

private theorem mem_of_set
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {a : WeylGroup .E6}
    {n : ModGL .E6 L} (hnE : n ∈ E)
    (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {β : Fin Tag.E6.rank → ℤ}
    (hβ : β + a • β + a • (a • β) = 0)
    {d : ModGL .E6 L}
    (hdAll : ∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
      (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ (3 ^ m))
    (hd3 : d ^ 3 = 1) :
    ∃ x : Fin Tag.E6.rank → ZMod 3,
      (∀ a' ∈ A, adAct .E6 3 a' x = x) ∧
      d = rootDiagUnit .E6 (zetaVec ζ hζ x) ∧
      (∑ i, ((β i : ZMod 3) * x i)) = 0 := by
  obtain ⟨t, htT, htcomm, hdt, hdE⟩ :=
    exists_cube_root_of_power hL hEM hE hcard hET hAS hAg hdAll hd3
  have hdT : d ∈ torusGroup .E6 L := by
    rw [hdt]
    exact pow_mem htT 3
  obtain ⟨x, hxfix, hxd⟩ := exists_fixed_rootDiag hEM hE hEA hζo hζ hdE hdT
  obtain ⟨v, hv⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
  have hv3 : v ^ 3 = zetaVec ζ hζ x := by
    apply rootDiagUnit_injective (τ := .E6) (K := L)
    have ht3 : rootDiagUnit .E6 (v ^ 3) = t ^ 3 := by
      rw [← rootDiagUnit_pow]
      exact congrArg (fun s : ModGL .E6 L => s ^ 3) hv.symm
    exact ht3.trans (hdt.symm.trans hxd)
  exact ⟨x, hxfix, hxd, form_eq_zero_of_torus_root hEM hnE hnρ hζo hζ hβ htcomm hv hv3⟩

private theorem adAct_zero_E6 (a : WeylGroup .E6) :
    adAct .E6 3 a (0 : Fin Tag.E6.rank → ZMod 3) = 0 := by
  have h := NoOffRest.adAct_add (τ := .E6) (p := 3) a
    (0 : Fin Tag.E6.rank → ZMod 3) (0 : Fin Tag.E6.rank → ZMod 3)
  have h' : adAct .E6 3 a 0 = adAct .E6 3 a 0 + adAct .E6 3 a 0 := by simpa using h
  exact (add_left_cancel h').symm

private def fixSubmodule (A : Subgroup (WeylGroup .E6)) :
    Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3) where
  carrier := {x | ∀ a ∈ A, adAct .E6 3 a x = x}
  add_mem' := by
    intro x y hx hy a ha
    change adAct .E6 3 a (x + y) = x + y
    rw [NoOffRest.adAct_add, hx a ha, hy a ha]
  zero_mem' := by
    intro a ha
    exact adAct_zero_E6 a
  smul_mem' := by
    intro c x hx a ha
    change adAct .E6 3 a (c • x) = c • x
    rw [adAct_smul, hx a ha]

private def betaHom (V : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3))
    (β : Fin Tag.E6.rank → ℤ) : V →ₗ[ZMod 3] ZMod 3 where
  toFun x := ∑ i, ((β i : ZMod 3) * x.1 i)
  map_add' := by
    intro x y
    simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RingHom.id_apply]
    ring

private theorem card_fixSubmodule
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    (hAS : A ≤ modelHomE6.range) (hAcard : Nat.card A = 3)
    (hAne : A ≠ ⊥) (hAgA : ∀ i, A ≠ Subgroup.zpowers (gE6 i))
    {ζ : Lˣ} (hζo : orderOf ζ = 3) :
    Nat.card (fixSubmodule A) = 27 := by
  have h := card_mul_card_fix_eq hζo hEM hE
    (le_of_eq hcard.symm) hEA hAS hAne hAgA
  rw [hAcard] at h
  change Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
    ∀ a ∈ A, adAct .E6 3 a x = x} = 27
  omega

private theorem card_betaHom_ker
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    (hAS : A ≤ modelHomE6.range) (hAcard : Nat.card A = 3)
    (hAne : A ≠ ⊥) (hAgA : ∀ i, A ≠ Subgroup.zpowers (gE6 i))
    {ζ : Lˣ} (hζo : orderOf ζ = 3)
    {β : Fin Tag.E6.rank → ℤ} {x0 : Fin Tag.E6.rank → ZMod 3}
    (hx0 : x0 ∈ fixSubmodule A)
    (hβx0 : (∑ i, ((β i : ZMod 3) * x0 i)) ≠ 0) :
    Nat.card (betaHom (fixSubmodule A) β).ker = 9 := by
  let f : fixSubmodule A →ₗ[ZMod 3] ZMod 3 := betaHom (fixSubmodule A) β
  let x0V : fixSubmodule A := ⟨x0, hx0⟩
  have hf0 : f x0V ≠ 0 := by
    dsimp [f, betaHom, x0V]
    exact hβx0
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨(y * (f x0V)⁻¹) • x0V, ?_⟩
    rw [map_smul, smul_eq_mul]
    rw [mul_assoc, inv_mul_cancel₀ hf0, mul_one]
  have hV : Nat.card (fixSubmodule A) = 27 :=
    card_fixSubmodule hEM hE hcard hEA hAS hAcard hAne hAgA hζo
  letI : AddCommGroup (ZMod 3) := (ZMod.instField 3).toAddCommGroup
  have hcard := Submodule.card_eq_card_quotient_mul_card (R := ZMod 3)
    (M := fixSubmodule A) f.ker
  have hquot : Nat.card (fixSubmodule A ⧸ f.ker) = 3 := by
    rw [Nat.card_congr (LinearMap.quotKerEquivOfSurjective f hsurj).toEquiv,
      Nat.card_zmod]
  rw [hV, hquot] at hcard
  have h9 : Nat.card f.ker = 9 := by omega
  simpa [f] using h9

private theorem exists_zeta_order_three {L : Type} [Field L] [IsAlgClosed L]
    (hL : ringChar L ≠ 3) : ∃ ζ : Lˣ, orderOf ζ = 3 ∧ ζ ^ 3 = 1 := by
  have h3L : (3 : L) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime L (p := ringChar L) Nat.prime_three hL
  obtain ⟨ζ, hζo⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (k := L) (n := 3) h3L
  exact ⟨ζ, hζo, hζo ▸ pow_orderOf_eq_one ζ⟩

private theorem modelData_of_generator
    {L : Type} [Field L]
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    {n : ModGL .E6 L} (hnE : n ∈ E)
    {a : WeylGroup .E6}
    (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (haine : ∀ i, a ≠ gE6 i) (hainv : ∀ i, a ≠ (gE6 i)⁻¹) :
    ∃ y : Model piE7 piE7_pow_three, ∃ β : Fin Tag.E6.rank → ℤ,
      ∃ x0 : Fin Tag.E6.rank → ZMod 3,
        modelHomE6 y = a ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧
        β + a • β + a • (a • β) = 0 ∧
        adAct .E6 3 a x0 = x0 ∧
        (∑ i, ((β i : ZMod 3) * x0 i)) ≠ 0 := by
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 (hAS n hnE)
  have hya : modelHomE6 y = a := hy.trans hnρ
  have hy3 : y ^ 3 = 1 := by
    apply modelHomE6_injective
    rw [map_pow, hya, ha3, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    apply ha1
    rw [← hya, h, map_one]
  have hyg : ∀ i, modelHomE6 y ≠ gE6 i := fun i => by rw [hya]; exact haine i
  have hygi : ∀ i, modelHomE6 y ≠ (gE6 i)⁻¹ := fun i => by rw [hya]; exact hainv i
  obtain ⟨β, x0, hβ, hx0, hdot⟩ := modelData_exists y hy3 hy1 hyg hygi
  rw [hya] at hβ hx0
  exact ⟨y, β, x0, hya, hy3, hy1, hβ, hx0, hdot⟩

private def admissibleSet {L : Type} [Field L] (E : Subgroup (ModGL .E6 L)) :
    Set (ModGL .E6 L) :=
  {d | (∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
    (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ d ^ 3 = 1}

private def kernelSet (V : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3))
    (f : V →ₗ[ZMod 3] ZMod 3) : Set (Fin Tag.E6.rank → ZMod 3) :=
  {x | ∃ hx : x ∈ V, f ⟨x, hx⟩ = 0}

private theorem kernelSet_encard (V : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3))
    (f : V →ₗ[ZMod 3] ZMod 3) : (kernelSet V f).encard = Nat.card f.ker := by
  have h : kernelSet V f =
      (fun k : f.ker => (k.1.1 : Fin Tag.E6.rank → ZMod 3)) '' Set.univ := by
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨⟨x, hx⟩, hfx⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨k, -, rfl⟩
      exact ⟨k.1.2, k.2⟩
  rw [h, Set.InjOn.encard_image]
  · rw [Set.encard_univ, ENat.card_eq_coe_natCard]
  · intro p _ q _ hpq
    exact Subtype.ext (Subtype.ext hpq)

private theorem admissibleSet_subset_kernel_image
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {a : WeylGroup .E6} {n : ModGL .E6 L} (hnE : n ∈ E)
    (hnρ : weylQuotientHom .E6 L ⟨n, hEM hnE⟩ = a)
    {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {β : Fin Tag.E6.rank → ℤ}
    (hβ : β + a • β + a • (a • β) = 0) :
    admissibleSet E ⊆ (fun x => rootDiagUnit .E6 (zetaVec ζ hζ x)) ''
      kernelSet (fixSubmodule A) (betaHom (fixSubmodule A) β) := by
  rintro d ⟨hdAll, hd3⟩
  obtain ⟨x, hxfix, hxd, hxdot⟩ :=
    mem_of_set hL hEM hE hcard hET hAS hAg hEA hnE hnρ hζo hζ hβ hdAll hd3
  refine ⟨x, ?_, hxd.symm⟩
  exact ⟨hxfix, by
    dsimp [betaHom]
    exact hxdot⟩

private theorem rootDiag_zetaVec_injective
    {L : Type} [Field L]
    {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Function.Injective (fun x : Fin Tag.E6.rank → ZMod 3 =>
      rootDiagUnit .E6 (zetaVec ζ hζ x)) := by
  intro x y hxy
  exact zetaVec_injective hζo hζ (rootDiagUnit_injective hxy)

private theorem fixed_of_zpowers_gen {A : Subgroup (WeylGroup .E6)}
    {a : WeylGroup .E6} (hAeq : A = Subgroup.zpowers a) (ha3 : a ^ 3 = 1)
    {x0 : Fin Tag.E6.rank → ZMod 3} (hx0 : adAct .E6 3 a x0 = x0) :
    x0 ∈ fixSubmodule A := by
  have hx0pow : ∀ r : ℕ, adAct .E6 3 (a ^ r) x0 = x0 := by
    intro r
    induction r with
    | zero => rw [pow_zero, adAct_one]
    | succ r ih => rw [pow_succ, adAct_mul, hx0, ih]
  intro a' ha'
  rw [hAeq] at ha'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ha'
  rw [← hk]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  let r : ℕ := (k % 3).toNat
  have hr : (r : ℤ) = k % 3 := Int.toNat_of_nonneg h0
  have hr3 : r < 3 := by omega
  have hkmod : a ^ k = a ^ r := by
    have ha3z : a ^ (3 : ℤ) = 1 := by simpa using ha3
    rw [zpow_eq_zpow_emod k ha3z]
    rw [show k % (3 : ℤ) = (r : ℤ) from hr.symm]
    exact zpow_natCast a r
  rw [hkmod]
  interval_cases r <;>
    simp [pow_zero, pow_one, pow_two, adAct_one, adAct_mul, hx0]

theorem encard_le_nine
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    (hA3 : Nat.card ((E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L)) = 3) :
    {d : ModGL .E6 L | (∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
      (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ d ^ 3 = 1}.encard ≤ 9 := by
  classical
  obtain ⟨A, hAcard, hEA, hAS', hA, hAne, hAgA, n, hnE, a, hnρ, hAeq, ha3, ha1,
    haine, hainv⟩ := exists_weylGenerator hEM hE hET hAS hAg hA3
  obtain ⟨ζ, hζo, hζ⟩ := exists_zeta_order_three hL
  obtain ⟨y, β, x0, hya, hy3, hy1, hβ, hx0, hdot⟩ :=
    modelData_of_generator hEM hAS hnE hnρ ha3 ha1 haine hainv
  have hx0V : x0 ∈ fixSubmodule A := fixed_of_zpowers_gen hAeq ha3 hx0
  have hβx0 : (∑ i, ((β i : ZMod 3) * x0 i)) ≠ 0 := hdot
  have hcardker : Nat.card (betaHom (fixSubmodule A) β).ker = 9 :=
    card_betaHom_ker hEM hE hcard hEA hAS' hAcard hAne hAgA hζo hx0V hβx0
  have hsub := admissibleSet_subset_kernel_image hL hEM hE hcard hET hAS hAg hEA
    hnE hnρ hζo hζ hβ
  have hinj := rootDiag_zetaVec_injective hζo hζ
  change (admissibleSet E).encard ≤ 9
  calc (admissibleSet E).encard ≤
      ((fun x => rootDiagUnit .E6 (zetaVec ζ hζ x)) ''
        kernelSet (fixSubmodule A) (betaHom (fixSubmodule A) β)).encard :=
        Set.encard_mono hsub
    _ = (kernelSet (fixSubmodule A) (betaHom (fixSubmodule A) β)).encard :=
        Set.InjOn.encard_image (fun x _ y _ h => hinj h)
    _ = Nat.card (betaHom (fixSubmodule A) β).ker :=
        kernelSet_encard (fixSubmodule A) (betaHom (fixSubmodule A) β)
    _ = 9 := by rw [hcardker]; norm_num
end CFSG.StandardType.E6NonToralThree
