module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Proposition93
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary85
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Section4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Focal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Residual
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Lemma 10.1

This file starts the Corollary 8.5 analysis used in Lemma 10.1.  For the
normal subgroup supplied by Proposition 9.3 it identifies the local
normalizer with `V`, extracts the factorization `V = A₁ P`, and records the
nontrivial/disjoint centralizer factor needed for source `(10B)`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise
open scoped IsMulCommutative

universe u

/-- A subgroup of `H` whose `p'`-core is normal there lies in the mapped
ambient `p'`-core of `H`. -/
private theorem subgroupOf_le_pPrimeCore_map
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K H : Subgroup G} (hKH : K ≤ H) [hKN : (K.subgroupOf H).Normal]
    (hcop : Nat.Coprime p (Nat.card K)) :
    K ≤ (pPrimeCore p ↥H).map H.subtype := by
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hcop' : Nat.Coprime p (Nat.card (K.subgroupOf H)) := by
    rw [hcard]
    exact hcop
  have hsub : K.subgroupOf H ≤ pPrimeCore p ↥H :=
    le_sSup ⟨hKN, hcop'⟩
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKH] using
    (Subgroup.map_mono (f := H.subtype) hsub)

/-- A subgroup normal in `V` has full normalizer inside `V`. -/
public theorem normalizerIn_eq_self_of_le_of_normal
    {X : Type u} [Group X]
    {V Y : Subgroup X}
    (hYV : Y ≤ V)
    (hY : (Y.subgroupOf V).Normal) :
    normalizerIn V Y = V := by
  apply le_antisymm
  · exact inf_le_left
  · intro v hv
    exact ⟨hv,
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYV).mp hY hv⟩

/-- The normalizer half of `[II1; 4.3(a)]` follows from the existing
Peterfalvi decomposition theorem.  Thus only the coprimality conclusion of
that source lemma remains as an external input to Lemma 10.1. -/
public theorem lemma101_normalizer_eq_of_fixedPointFree
    {X : Type u} [Group X] [Finite X]
    {D P : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : rightConjugate D t = D)
    (hP : P ≤ peterfalviV D t)
    (hPne : P ≠ ⊥)
    (hfixed : PeterfalviCentralizersTrivial D t P) :
    normalizerIn D P = normalizerIn (peterfalviV D t) P := by
  classical
  let N : Subgroup X := normalizerIn D P
  have hDforward {d : X} (hd : d ∈ D) :
      rightConjugateElem d t ∈ D := by
    have hmem := rightConjugateElem_mem_rightConjugate (g := t) hd
    simpa [hDnorm] using hmem
  have htCentralizesP :
      t ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgC : g ∈ Subgroup.centralizer ({t} : Set X) := (hP hg).2
    exact Subgroup.mem_centralizer_singleton_iff.mp hgC
  have htNormP : t ∈ Subgroup.normalizer (P : Set X) :=
    centralizer_le_normalizer P htCentralizesP
  have hNforward {n : X} (hn : n ∈ N) :
      rightConjugateElem n t ∈ N := by
    refine ⟨hDforward hn.1, ?_⟩
    change t⁻¹ * n * t ∈ Subgroup.normalizer (P : Set X)
    exact (Subgroup.normalizer (P : Set X)).mul_mem
      ((Subgroup.normalizer (P : Set X)).mul_mem
        ((Subgroup.normalizer (P : Set X)).inv_mem htNormP) hn.2)
      htNormP
  have htNormN : t ∈ Subgroup.normalizer (N : Set X) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro n
    change n ∈ N ↔ rightConjugateElem n t ∈ N
    constructor
    · exact hNforward
    · intro hnt
      have hback := hNforward hnt
      simpa [rightConjugateElem_rightConjugateElem ht.inv_eq_self] using hback
  have hNodd : Odd (Nat.card N) := by
    apply hDodd.of_dvd_nat
    exact Subgroup.card_dvd_of_le inf_le_left
  apply le_antisymm
  · intro n hn
    have hdecomp := (PFchapter1section1.lemma_a t N ht hNodd htNormN).1
    obtain ⟨yz, _hyz, hyzEq⟩ := hdecomp.surjOn hn
    let y : X := yz.1
    let z : X := yz.2
    have hyN : y ∈ N := yz.1.property.1
    have hyC : y ∈ Subgroup.centralizer ({t} : Set X) := yz.1.property.2
    have hzN : z ∈ N := yz.2.property.1
    have hzAnti : rightConjugateElem z t = z⁻¹ := yz.2.property.2
    obtain ⟨g, hgne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
    have hgP : (g : X) ∈ P := g.property
    have hzgComm : z * (g : X) = (g : X) * z := by
      have hzInvNormP : z⁻¹ ∈ Subgroup.normalizer (P : Set X) :=
        (Subgroup.normalizer (P : Set X)).inv_mem hzN.2
      have hgConjP : rightConjugateElem (g : X) z ∈ P := by
        simpa [rightConjugateElem] using
          (Subgroup.mem_normalizer_iff.mp hzInvNormP (g : X)).1 hgP
      have hgConjFixed :
          rightConjugateElem (rightConjugateElem (g : X) z) t =
            rightConjugateElem (g : X) z := by
        have hmemV := hP hgConjP
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hmemV.2
        have htt : t * t = 1 := by
          simpa [pow_two] using ht.sq_eq_one
        calc
          rightConjugateElem (rightConjugateElem (g : X) z) t =
              t * rightConjugateElem (g : X) z * t := by
            rw [rightConjugateElem, ht.inv_eq_self]
          _ = rightConjugateElem (g : X) z * (t * t) := by
            rw [hcomm.symm, mul_assoc]
          _ = rightConjugateElem (g : X) z := by simp [htt]
      have hgFixed : rightConjugateElem (g : X) t = (g : X) := by
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hP hgP).2
        have htt : t * t = 1 := by
          simpa [pow_two] using ht.sq_eq_one
        calc
          rightConjugateElem (g : X) t = t * (g : X) * t := by
            rw [rightConjugateElem, ht.inv_eq_self]
          _ = (g : X) * (t * t) := by rw [hcomm.symm, mul_assoc]
          _ = (g : X) := by simp [htt]
      have hzAntiInv : rightConjugateElem z⁻¹ t = z := by
        calc
          rightConjugateElem z⁻¹ t = (rightConjugateElem z t)⁻¹ := by
            simp [rightConjugateElem, mul_assoc]
          _ = z := by rw [hzAnti]; simp
      have hconjEq :
          rightConjugateElem (g : X) z =
            rightConjugateElem (g : X) z⁻¹ := by
        calc
          rightConjugateElem (g : X) z =
              t⁻¹ * rightConjugateElem (g : X) z * t := by
            simpa [rightConjugateElem] using hgConjFixed.symm
          _ = (t⁻¹ * z⁻¹ * t) * (t⁻¹ * (g : X) * t) *
                (t⁻¹ * z * t) := by
            simp only [rightConjugateElem]
            group
          _ = z * (g : X) * z⁻¹ := by
            rw [show t⁻¹ * z⁻¹ * t = z by
                  simpa [rightConjugateElem] using hzAntiInv,
              show t⁻¹ * (g : X) * t = (g : X) by
                simpa [rightConjugateElem] using hgFixed,
              show t⁻¹ * z * t = z⁻¹ by
                simpa [rightConjugateElem] using hzAnti]
          _ = rightConjugateElem (g : X) z⁻¹ := by
            simp [rightConjugateElem]
      have hzSqComm : Commute (z ^ 2) (g : X) := by
        rw [pow_two]
        change (z * z) * (g : X) = (g : X) * (z * z)
        calc
          (z * z) * (g : X) = z * (z * (g : X) * z⁻¹) * z := by group
          _ = z * (z⁻¹ * (g : X) * z) * z := by
            simpa [rightConjugateElem] using
              congrArg (fun q : X => z * q * z) hconjEq.symm
          _ = (g : X) * (z * z) := by group
      have hzOrderOdd : Odd (orderOf z) := by
        apply hDodd.of_dvd_nat
        simpa using orderOf_dvd_natCard (⟨z, hzN.1⟩ : D)
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
        (x := z) (n := 2) hzOrderOdd.coprime_two_left
      have hzComm : Commute z (g : X) := by
        rw [← hm]
        simpa [pow_mul] using hzSqComm.pow_left m
      exact hzComm.eq
    have hzI : z ∈ peterfalviKSet D t := ⟨hzN.1, hzAnti⟩
    have hzOne : z = 1 :=
      hfixed (g : X) hgP (by simpa using hgne) z hzI hzgComm
    have hnEqY : n = y := by
      change n = y
      change y * z = n at hyzEq
      simpa [hzOne] using hyzEq.symm
    rw [hnEqY]
    exact ⟨⟨hyN.1, hyC⟩, hyN.2⟩
  · intro n hn
    exact ⟨hn.1.1, hn.2⟩

/-- The subgroup generated by the Peterfalvi anti-fixed set is normal in
`D`.  This is checked algebra from `PFchapter1section1.lemma_b`; it is not an
additional source callback for Lemma 10.1. -/
public theorem lemma101_peterfalviKernel_normal
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X)) :
    ((Subgroup.closure (peterfalviKSet D t)).subgroupOf D).Normal := by
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let Z : Set D :=
    {x : D | rightConjugateElem (x : X) t = (x : X)⁻¹}
  let L : Subgroup D := Subgroup.closure Z
  have hKD : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have himage : D.subtype '' Z = peterfalviKSet D t := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hmapL : L.map D.subtype = K := by
    simp only [L, K, MonoidHom.map_closure, himage]
  have hEq : K.subgroupOf D = L := by
    apply Subgroup.map_injective D.subtype_injective
    calc
      (K.subgroupOf D).map D.subtype = K := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKD]
      _ = L.map D.subtype := hmapL.symm
  rw [show Subgroup.closure (peterfalviKSet D t) = K from rfl]
  rw [hEq]
  simpa [L, Z] using PFchapter1section1.lemma_b t D ht hDodd hDnorm

/-- The Peterfalvi decomposition gives `D = K V`, with `K` the subgroup
generated by the anti-fixed set and `V = C_D(t)`. -/
public theorem lemma101_peterfalviKernel_sup_fixed_eq
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X)) :
    Subgroup.closure (peterfalviKSet D t) ⊔ peterfalviV D t = D := by
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  have hKD : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hVD : V ≤ D := inf_le_left
  apply le_antisymm
  · exact sup_le hKD hVD
  · intro d hd
    obtain ⟨yz, _hyz, hyzEq⟩ :=
      (PFchapter1section1.lemma_a t D ht hDodd hDnorm).1.surjOn hd
    have hyV : (yz.1 : X) ∈ V := yz.1.property
    have hzK : (yz.2 : X) ∈ K :=
      Subgroup.subset_closure yz.2.property
    change d ∈ K ⊔ V
    rw [← hyzEq]
    exact (K ⊔ V).mul_mem
      ((show V ≤ K ⊔ V from le_sup_right) hyV)
      ((show K ≤ K ⊔ V from le_sup_left) hzK)

private theorem lemma101_inf_le_complement_of_coprime
    {X : Type u} [Group X] [Finite X]
    {K V A P : Subgroup X} {p : ℕ}
    (hAV : A ≤ V) (hPV : P ≤ V)
    (hAnormal : (A.subgroupOf V).Normal)
    (hsup : A ⊔ P = V)
    (hdisj : Disjoint A P)
    (hPcard : Nat.card P = p)
    (hcop : Nat.Coprime p (Nat.card K)) :
    K ⊓ V ≤ A := by
  let AV : Subgroup V := A.subgroupOf V
  let PV : Subgroup V := P.subgroupOf V
  let R : Subgroup X := K ⊓ V
  let RV : Subgroup V := R.subgroupOf V
  let q : V →* V ⧸ AV := QuotientGroup.mk' AV
  letI : AV.Normal := by simpa [AV] using hAnormal
  have hsupV : AV ⊔ PV = ⊤ := by
    calc
      AV ⊔ PV = (A ⊔ P).subgroupOf V := by
        simpa [AV, PV] using (Subgroup.subgroupOf_sup hAV hPV).symm
      _ = V.subgroupOf V := by rw [hsup]
      _ = ⊤ := Subgroup.subgroupOf_self V
  have hdisjV : Disjoint PV AV := by
    rw [Subgroup.disjoint_def]
    intro x hxP hxA
    have hxOne : (x : X) = 1 :=
      Subgroup.disjoint_def.mp hdisj hxA hxP
    exact Subtype.ext hxOne
  have hmulV : (PV : Set V) * (AV : Set V) = Set.univ := by
    rw [← Subgroup.mul_normal PV AV, sup_comm, hsupV]
    rfl
  have hcomp : PV.IsComplement' AV :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjV hmulV
  have hquotCard : Nat.card (V ⧸ AV) = p := by
    calc
      Nat.card (V ⧸ AV) = AV.index := by
        rw [Subgroup.index_eq_card]
      _ = Nat.card PV := hcomp.index_eq_card
      _ = Nat.card P := natCard_subgroupOf_eq P V hPV
      _ = p := hPcard
  have hRVcard : Nat.card RV = Nat.card R :=
    natCard_subgroupOf_eq R V inf_le_right
  have hRdvdK : Nat.card R ∣ Nat.card K :=
    Subgroup.card_dvd_of_le inf_le_left
  have hcopR : Nat.Coprime p (Nat.card R) :=
    Nat.Coprime.of_dvd_right hRdvdK hcop
  have hmapDvdR : Nat.card (RV.map q) ∣ Nat.card R := by
    rw [← hRVcard]
    exact Subgroup.card_map_dvd RV q
  have hmapDvdP : Nat.card (RV.map q) ∣ p := by
    rw [← hquotCard]
    simpa only [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le
        (H := RV.map q) (K := (⊤ : Subgroup (V ⧸ AV))) le_top)
  have hmapCard : Nat.card (RV.map q) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopR hmapDvdP hmapDvdR
  have hmapBot : RV.map q = ⊥ := Subgroup.card_eq_one.mp hmapCard
  have hRVker : RV ≤ q.ker := (Subgroup.map_eq_bot_iff RV).mp hmapBot
  intro x hx
  let xV : V := ⟨x, hx.2⟩
  have hxRV : xV ∈ RV := hx
  have hxker : xV ∈ q.ker := hRVker hxRV
  change x ∈ A
  simpa [q, AV, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] using hxker

private theorem lemma101_conjugate_mem_sup_of_normalizes
    {G : Type*} [Group G] {A B : Subgroup G} {x y : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G))
    (hy : y ∈ A ⊔ B) :
    x * y * x⁻¹ ∈ A ⊔ B := by
  rw [Subgroup.sup_eq_closure] at hy ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with hzA | hzB
    · exact Subgroup.subset_closure
        (Or.inl ((Subgroup.mem_normalizer_iff.mp hA z).1 hzA))
    · exact Subgroup.subset_closure
        (Or.inr ((Subgroup.mem_normalizer_iff.mp hB z).1 hzB))
  · simp
  · intro a b _ha _hb hca hcb
    simpa [mul_assoc] using
      (Subgroup.closure ((A : Set G) ∪ (B : Set G))).mul_mem hca hcb
  · intro a _ha hca
    simpa [mul_assoc] using
      (Subgroup.closure ((A : Set G) ∪ (B : Set G))).inv_mem hca

private theorem lemma101_le_normalizer_sup_of_normalizes
    {G : Type*} [Group G] {A B S : Subgroup G}
    (hA : S ≤ Subgroup.normalizer (A : Set G))
    (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact lemma101_conjugate_mem_sup_of_normalizes (hA hx) (hB hx)
  · intro hy
    have hAinv : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem (hA hx)
    have hBinv : x⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normalizer (B : Set G)).inv_mem (hB hx)
    have h := lemma101_conjugate_mem_sup_of_normalizes
      (A := A) (B := B) (x := x⁻¹) (y := x * y * x⁻¹)
      hAinv hBinv hy
    simpa [mul_assoc] using h

/-- A subgroup normalizer also normalizes the corresponding centralizer. -/
public theorem le_normalizer_centralizer_of_le_normalizer
    {X : Type u} [Group X] {V J : Subgroup X}
    (hVJ : V ≤ Subgroup.normalizer (J : Set X)) :
    V ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set X) : Set X) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro j hj
    have hvInv : v⁻¹ ∈ Subgroup.normalizer (J : Set X) :=
      (Subgroup.normalizer (J : Set X)).inv_mem (hVJ hv)
    have hj' : v⁻¹ * j * (v⁻¹)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp hvInv j).mp hj
    have hcomm := hc (v⁻¹ * j * v) (by simpa using hj')
    calc
      j * (v * c * v⁻¹) = v * ((v⁻¹ * j * v) * c) * v⁻¹ := by group
      _ = v * (c * (v⁻¹ * j * v)) * v⁻¹ := by rw [hcomm]
      _ = (v * c * v⁻¹) * j := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro j hj
    have hj' : v * j * v⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hVJ hv) j).mp hj
    have hcomm := hc (v * j * v⁻¹) hj'
    calc
      j * c = v⁻¹ * ((v * j * v⁻¹) * (v * c * v⁻¹)) * v := by group
      _ = v⁻¹ * ((v * c * v⁻¹) * (v * j * v⁻¹)) * v := by rw [hcomm]
      _ = c * j := by group

/-- Hall's `p`-residual agrees with the equivalent Huppert residual used by
the commutator theorem in IV.3.3. -/
public theorem hallPResidual_eq_hktPResidual
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    External.hallPResidual p G = External.hktPResidual p G := by
  apply le_antisymm
  · let N : Subgroup G := External.hktPResidual p G
    letI : N.Normal := External.hktPResidual_normal (Q := G) (q := p)
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    have hq : IsPGroup p (G ⧸ N) := by
      simpa [N] using
        (External.hktPResidual_quotient_isPGroup (Q := G) (q := p))
    have hk : q.ker = N := by
      simpa [q, N] using (QuotientGroup.ker_mk' N)
    intro x hx
    have hkill : q x = 1 :=
      (External.hallPResidual_le_ker_of_isPGroup q hq) hx
    have hxN : x ∈ N := by
      rw [← hk]
      exact hkill
    exact hxN
  · let N : Subgroup G := External.hallPResidual p G
    letI : N.Normal := External.hallPResidual_normal p G
    have hq : IsPGroup p (G ⧸ N) := by
      simpa [N] using
        (External.hallPResidual_quotient_isPGroup (G := G) p)
    exact External.hktPResidual_le N (External.hallPResidual_normal p G) hq

/-- If an ambient Sylow subgroup lies in `D`, minimality forces the Hall
`p`-residual of the fixed normal supplement `W` to be all of `W`. -/
public theorem hallPResidual_eq_top_of_minimalNormalSupplement
    {X : Type*} [Group X] [Finite X]
    {M D W : Subgroup X} {p : ℕ} [Fact p.Prime]
    (hW : IsMinimalNormalSupplement M D W)
    (Q : Sylow p M)
    (hQD : (Q : Subgroup M) ≤ D.subgroupOf M) :
    External.hallPResidual p W = ⊤ := by
  classical
  let WM : Subgroup M := W.subgroupOf M
  letI : WM.Normal := hW.prop.normal_in_M
  let QW : Sylow p WM := External.hallSylowSubgroupOfNormal Q WM
  let eWM : WM ≃* W := Subgroup.subgroupOfEquivOfLe hW.prop.le_M
  let SW : Sylow p W := QW.mapSurjective (f := eWM.toMonoidHom) eWM.surjective
  let EW : Subgroup W := (W ⊓ D).subgroupOf W
  have hSW_EW : (SW : Subgroup W) ≤ EW := by
    intro x hx
    change x ∈ (QW : Subgroup WM).map eWM.toMonoidHom at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyQW, hyx⟩
    have hyQ : (y : M) ∈ (Q : Subgroup M) := by
      change y ∈ (Q : Subgroup M).comap WM.subtype
      rw [← External.hallSylowSubgroupOfNormal_coe Q WM]
      exact hyQW
    have hyD : ((y : WM) : M) ∈ D.subgroupOf M := hQD hyQ
    have hxval : (x : X) = (((y : WM) : M) : X) :=
      congrArg (fun z : W => (z : X)) hyx.symm
    refine ⟨x.2, ?_⟩
    have hyD' : (((y : WM) : M) : X) ∈ D := hyD
    have hxD : (x : X) ∈ D := by
      rw [hxval]
      exact hyD'
    exact hxD
  have hfac : EW ⊔ External.hallPResidual p W = ⊤ :=
    External.hall_sup_hallPResidual_eq_top_of_sylow_le p SW EW hSW_EW
  let RW : Subgroup W := External.hallPResidual p W
  let R : Subgroup X := RW.map W.subtype
  have hRleW : R ≤ W := Subgroup.map_subtype_le RW
  have hRnormal : (R.subgroupOf M).Normal := by
    exact normal_subgroupOf_map_of_characteristic_of_normal
      W R M hW.prop.le_M hW.prop.normal_in_M RW inferInstance rfl
        (hRleW.trans hW.prop.le_M)
  have hRsup : R ⊔ D = M := by
    have hEWmap : EW.map W.subtype = W ⊓ D := by
      simp [EW, Subgroup.subgroupOf_map_subtype, inf_comm]
    have htopmap : (⊤ : Subgroup W).map W.subtype = W := by
      rw [← MonoidHom.range_eq_map, Subgroup.subtype_range]
    have hmapfac : R ⊔ (W ⊓ D) = W := by
      calc
        R ⊔ (W ⊓ D) = RW.map W.subtype ⊔ EW.map W.subtype := by
          change RW.map W.subtype ⊔ (W ⊓ D) = _
          rw [hEWmap]
        _ = (RW ⊔ EW).map W.subtype :=
          (Subgroup.map_sup _ _ _).symm
        _ = (⊤ : Subgroup W).map W.subtype := by
          rw [sup_comm RW EW, hfac]
        _ = W := htopmap
    calc
      R ⊔ D = R ⊔ ((W ⊓ D) ⊔ D) := by
        rw [sup_eq_right.mpr (show W ⊓ D ≤ D from inf_le_right)]
      _ = (R ⊔ (W ⊓ D)) ⊔ D := by rw [sup_assoc]
      _ = W ⊔ D := by rw [hmapfac]
      _ = M := hW.prop.sup_eq
  have hRnormsupp : IsNormalSupplement M D R :=
    { le_M := hRleW.trans hW.prop.le_M
      normal_in_M := hRnormal
      sup_eq := hRsup }
  have hReq : R = W := hW.eq_of_le hRnormsupp hRleW
  have htopmap : (⊤ : Subgroup W).map W.subtype = W := by
    rw [← MonoidHom.range_eq_map, Subgroup.subtype_range]
  apply Subgroup.map_injective W.subtype_injective
  simpa [RW, R, hReq] using htopmap.symm

/-- A `p`-subgroup of a group with no nontrivial `p`-group quotient lies in
the commutator subgroup. -/
public theorem isPGroup_le_commutator_of_hallPResidual_eq_top
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G}
    (hP : IsPGroup p P)
    (hres : External.hallPResidual p G = ⊤) :
    P ≤ commutator G := by
  classical
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  have hhkt : External.hktPResidual p G = ⊤ := by
    rw [← hallPResidual_eq_hktPResidual (G := G) (p := p)]
    exact hres
  have hab : External.hktAbelianPResidual p G = ⊤ := by
    apply top_unique
    rw [← hhkt]
    exact External.hktPResidual_le_hktAbelianPResidual
  have heq :=
    External.huppert_IV_3_3_sylow_inf_abelian_residual_eq_sylow_inf_commutator
      (Q := G) (q := p) S
  rw [hab, inf_top_eq] at heq
  intro x hxP
  have hxS : x ∈ (S : Subgroup G) := hPS hxP
  have hxinf : x ∈ (S : Subgroup G) ⊓ commutator G := by
    rw [← heq]
    exact hxS
  exact hxinf.2

/-- The focal equality extends from the selected Sylow subgroup to every
`p`-subgroup of the fusion-controlling subgroup. -/
public theorem inf_commutator_eq_of_controlsFusionIn_of_isPGroup
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (E U : Subgroup G) (Q : Sylow p G)
    (hQ : (Q : Subgroup G) ≤ E)
    (hU : U ≤ E)
    (hUp : IsPGroup p U)
    (hfusion : ControlsFusionIn E (Q : Subgroup G)) :
    U ⊓ commutator G =
      U ⊓ (commutator E).map E.subtype := by
  classical
  let UE : Subgroup E := U.subgroupOf E
  have hUEp : IsPGroup p UE :=
    hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hU).symm
  obtain ⟨R, hUER⟩ := hUEp.exists_le_sylow
  let QE : Sylow p E := Q.subtype hQ
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq E R QE
  let UE' : Subgroup E := (MulAut.conj e) • UE
  let U' : Subgroup G := UE'.map E.subtype
  have heSub : (MulAut.conj e) • (R : Subgroup E) =
      (QE : Subgroup E) := by
    simpa [Sylow.coe_subgroup_smul] using
      congrArg (fun S : Sylow p E => (S : Subgroup E)) he
  have hUE'QE : UE' ≤ (QE : Subgroup E) := by
    rw [← heSub]
    exact Subgroup.map_mono hUER
  have hU'Q : U' ≤ (Q : Subgroup G) := by
    intro x hx
    have hxmap : x ∈ (QE : Subgroup E).map E.subtype :=
      Subgroup.map_mono hUE'QE hx
    simpa [QE, Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hQ] using hxmap
  have hEq :=
    inf_commutator_eq_inf_map_commutator_of_controlsFusionIn
      E U' Q hQ hU'Q hfusion
  apply le_antisymm
  · intro x hx
    let xE : E := ⟨x, hU hx.1⟩
    let xE' : E := (MulAut.conj e) xE
    have hxE'_UE' : xE' ∈ UE' := by
      change (MulAut.conj e) xE ∈ (MulAut.conj e) • UE
      exact Subgroup.mem_map.mpr ⟨xE, hx.1, rfl⟩
    have hxE'_U' : (xE' : G) ∈ U' :=
      Subgroup.mem_map_of_mem E.subtype hxE'_UE'
    have hxE'_commG : (xE' : G) ∈ commutator G := by
      have hnormal : (commutator G).Normal := inferInstance
      have hconj := hnormal.conj_mem x hx.2 (e : G)
      simpa [xE', xE, MulAut.conj_apply] using hconj
    have hxE'_map : (xE' : G) ∈ (commutator E).map E.subtype := by
      have hxinf : (xE' : G) ∈ U' ⊓ commutator G :=
        ⟨hxE'_U', hxE'_commG⟩
      have hxinf' : (xE' : G) ∈
          U' ⊓ (commutator E).map E.subtype := by
        rw [← hEq]
        exact hxinf
      exact hxinf'.2
    rcases Subgroup.mem_map.mp hxE'_map with ⟨z, hz, hzx⟩
    have hzxE : z = xE' := Subtype.ext hzx
    have hxE'_commE : xE' ∈ commutator E := by simpa [hzxE] using hz
    have hnormalE : (commutator E).Normal := inferInstance
    have hback := hnormalE.conj_mem xE' hxE'_commE e⁻¹
    have hxE_commE : xE ∈ commutator E := by
      simpa [xE', xE, MulAut.conj_apply, mul_assoc] using hback
    refine ⟨hx.1, ?_⟩
    exact Subgroup.mem_map_of_mem E.subtype hxE_commE
  · intro x hx
    refine ⟨hx.1, ?_⟩
    rw [Subgroup.map_subtype_commutator] at hx
    exact Subgroup.commutator_mono le_top le_top hx.2

/-- The first Corollary 8.5 package in the proof of Lemma 10.1.  Here
`J = C_I(Y)` and `A₁ = C_V(J)`. -/
public structure Lemma101InitialData
    {X : Type u} [Group X] [Finite X]
    (D V Y P : Subgroup X) (t : X) where
  J : Subgroup X
  A1 : Subgroup X
  J_eq_centralizer :
    (J : Set X) =
      {x : X | x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (Y : Set X)}
  A1_eq : A1 = V ⊓ Subgroup.centralizer (J : Set X)
  card_P_prime : Nat.Prime (Nat.card P)
  J_card : Nat.card J = 2 ^ Nat.card P - 1
  P_le_V : P ≤ V
  V_eq_mul : (V : Set X) = (A1 : Set X) * (P : Set X)
  Y_le_A1 : Y ≤ A1
  A1_ne_bot : A1 ≠ ⊥
  A1_normal_V : (A1.subgroupOf V).Normal
  A1_disjoint_P : Disjoint A1 P

/-- Extract the initial Lemma 10.1 data from the already-proved Corollary
8.5 conclusion. -/
public theorem lemma101_initial_data_of_corollary85
    {X : Type u} [Group X] [Finite X]
    {M D V Y P : Subgroup X} {t u0 : X}
    (hD : D = M ⊓ rightConjugate M t)
    (hVeq : V = D ⊓ Subgroup.centralizer ({u0} : Set X))
    (hVt : V ≤ peterfalviV D t)
    (hYV : Y ≤ V) (hYne : Y ≠ ⊥)
    (hY : (Y.subgroupOf V).Normal)
    (hcentral : HasNontrivialPeterfalviCentralizer D t Y)
    (hPV : P ≤ V)
    (hfixed : PeterfalviCentralizersTrivial D t P)
    (h85 : Corollary85Conclusion M t u0 Y P) :
    Nonempty (Lemma101InitialData D V Y P t) := by
  classical
  let J : Subgroup X := h85.J
  let A1 : Subgroup X := V ⊓ Subgroup.centralizer (J : Set X)
  have hnorm : normalizerIn V Y = V :=
    normalizerIn_eq_self_of_le_of_normal hYV hY
  have hfactor := h85.local_normalizer_eq_mul_centralizer
  rw [← hD, ← hVeq, hnorm] at hfactor
  have hJset : (J : Set X) =
      {x : X | x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (Y : Set X)} := by
    simpa [J, hD] using h85.J_eq_centralizer
  have hYJ : Y ≤ Subgroup.centralizer (J : Set X) := by
    intro y hyY
    rw [Subgroup.mem_centralizer_iff]
    intro j hjJ
    have hj : j ∈ peterfalviKSet D t ∧
        j ∈ Subgroup.centralizer (Y : Set X) := by
      have hj' : j ∈ {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (Y : Set X)} := by
        rw [← hJset]
        exact hjJ
      exact hj'
    exact (Subgroup.mem_centralizer_iff.mp hj.2 y hyY).symm
  have hYA1 : Y ≤ A1 := le_inf hYV hYJ
  have hA1ne : A1 ≠ ⊥ := by
    intro hbot
    apply hYne
    exact eq_bot_iff.mpr (hYA1.trans_eq hbot)
  have hYnorm : V ≤ Subgroup.normalizer (Y : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYV).mp hY
  have hVnormJ : V ≤ Subgroup.normalizer (J : Set X) := by
    intro v hvV
    have hvVt : v ∈ peterfalviV D t := hVt hvV
    have hvCY :
        v ∈ Subgroup.normalizer
          (Subgroup.centralizer (Y : Set X) : Set X) :=
      le_normalizer_centralizer_of_le_normalizer hYnorm hvV
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · intro hjJ
      have hj : j ∈ peterfalviKSet D t ∧
          j ∈ Subgroup.centralizer (Y : Set X) := by
        change j ∈ (J : Set X) at hjJ
        exact (congrArg (fun S : Set X => j ∈ S) hJset).mp hjJ
      change v * j * v⁻¹ ∈ (J : Set X)
      rw [hJset]
      exact ⟨peterfalviKSet_conj_mem_of_mem_V hvVt hj.1,
        (Subgroup.mem_normalizer_iff.mp hvCY j).mp hj.2⟩
    · intro hjJ
      have hj : v * j * v⁻¹ ∈ peterfalviKSet D t ∧
          v * j * v⁻¹ ∈ Subgroup.centralizer (Y : Set X) := by
        change v * j * v⁻¹ ∈ (J : Set X) at hjJ
        exact
          (congrArg (fun S : Set X => v * j * v⁻¹ ∈ S) hJset).mp hjJ
      change j ∈ (J : Set X)
      rw [hJset]
      constructor
      · have hvInvVt : v⁻¹ ∈ peterfalviV D t :=
          (peterfalviV D t).inv_mem hvVt
        have hconj := peterfalviKSet_conj_mem_of_mem_V hvInvVt hj.1
        simpa [mul_assoc] using hconj
      · exact (Subgroup.mem_normalizer_iff.mp hvCY j).mpr hj.2
  have hA1normal : (A1.subgroupOf V).Normal := by
    change
      ((V ⊓ Subgroup.centralizer (J : Set X)).subgroupOf V).Normal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact Subgroup.le_normalizer_inf Subgroup.le_normalizer
      (le_normalizer_centralizer_of_le_normalizer hVnormJ)
  obtain ⟨j, hjI, hjCY, hjne⟩ := hcentral
  have hjJ : j ∈ J := by
    change j ∈ (J : Set X)
    rw [hJset]
    exact ⟨hjI, hjCY⟩
  have hdisj : Disjoint A1 P := by
    rw [Subgroup.disjoint_def]
    intro g hgA hgP
    by_contra hgne
    have hcomm : j * g = g * j :=
      Subgroup.mem_centralizer_iff.mp hgA.2 j hjJ
    exact hjne (hfixed g hgP hgne j hjI hcomm)
  exact ⟨{
    J := J
    A1 := A1
    J_eq_centralizer := hJset
    A1_eq := rfl
    card_P_prime := h85.card_P_prime
    J_card := by simpa [J] using h85.J_card
    P_le_V := hPV
    V_eq_mul := by simpa [J, A1] using hfactor
    Y_le_A1 := hYA1
    A1_ne_bot := hA1ne
    A1_normal_V := hA1normal
    A1_disjoint_P := hdisj }⟩

/-- The source choices at the start of Lemma 10.1: a prime in the
abelianization, its Corollary 9.5 Sylow subgroup inside `V`, and the
Proposition 9.3 subgroup to which Corollary 8.5 is applied. -/
public structure Lemma101ChoiceData
    {X : Type u} [Group X] [Finite X]
    (D E V : Subgroup X) (t : X) where
  p : ℕ
  p_prime : Nat.Prime p
  p_dvd_abelianization : p ∣ Nat.card (E ⧸ derivedSubgroup E)
  S : Sylow p E
  P : Subgroup X
  P_eq_map : P = (S : Subgroup E).map E.subtype
  S_cyclic : IsCyclic (S : Subgroup E)
  P_le_V : P ≤ V
  P_fixedPointFree : PeterfalviCentralizersTrivial D t P
  Y : Subgroup X
  Y_le_V : Y ≤ V
  Y_ne_bot : Y ≠ ⊥
  Y_normal_V : (Y.subgroupOf V).Normal
  Y_nontrivial_centralizer : HasNontrivialPeterfalviCentralizer D t Y
  initial : Lemma101InitialData D V Y P t

/-- The Corollary 8.5 prime-order conclusion identifies the chosen cyclic
Sylow subgroup's order with its defining prime. -/
public theorem Lemma101ChoiceData.card_P_eq
    {X : Type u} [Group X] [Finite X]
    {D E V : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E V t) :
    Nat.card d.P = d.p := by
  letI : Fact d.p.Prime := ⟨d.p_prime⟩
  have hcard : Nat.card d.P =
      d.p ^ (Nat.card E).factorization d.p := by
    calc
      Nat.card d.P = Nat.card (d.S : Subgroup E) := by
        rw [d.P_eq_map]
        exact Subgroup.card_map_of_injective E.subtype_injective
      _ = d.p ^ (Nat.card E).factorization d.p :=
        d.S.card_eq_multiplicity
  have hn : (Nat.card E).factorization d.p ≠ 0 := by
    intro hn
    have hPone : Nat.card d.P = 1 := by simp [hcard, hn]
    exact d.initial.card_P_prime.ne_one hPone
  have hpdiv : d.p ∣ Nat.card d.P := by
    rw [hcard]
    exact dvd_pow_self d.p hn
  rcases d.initial.card_P_prime.eq_one_or_self_of_dvd d.p hpdiv with
    hpone | hpP
  · exact False.elim (d.p_prime.ne_one hpone)
  · exact hpP.symm

/-- The chosen ambient subgroup is the image of a Sylow subgroup of `E`. -/
public theorem Lemma101ChoiceData.P_isSylow_E
    {X : Type u} [Group X] [Finite X]
    {D E V : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E V t) :
    theorem4bIsSylowSubgroupOf d.p d.P E := by
  exact ⟨d.S, d.P_eq_map⟩

/-- A Sylow subgroup in `D` that lies in an intermediate subgroup `E` is
still Sylow in `E`, in the ambient subgroup encoding used here. -/
public theorem theorem4bIsSylowSubgroupOf_of_between
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P E D : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P D)
    (hPE : P ≤ E) (hED : E ≤ D) :
    theorem4bIsSylowSubgroupOf p P E := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PD, hP⟩
  let ED : Subgroup D := E.subgroupOf D
  have hPDle : (PD : Subgroup D) ≤ ED := by
    intro x hx
    change (x : X) ∈ E
    apply hPE
    rw [hP]
    exact Subgroup.mem_map_of_mem D.subtype hx
  let PED : Sylow p ED := PD.subtype hPDle
  let e : ED ≃* E := Subgroup.subgroupOfEquivOfLe hED
  let PE : Sylow p E := PED.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨PE, ?_⟩
  apply le_antisymm
  · intro x hxP
    rw [hP] at hxP
    rcases Subgroup.mem_map.mp hxP with ⟨xD, hxPD, rfl⟩
    apply Subgroup.mem_map.mpr
    let xED : ED := ⟨xD, hPDle hxPD⟩
    refine ⟨e xED, ?_, rfl⟩
    have hxPED : xED ∈ PED := hxPD
    simpa [PE] using Subgroup.mem_map_of_mem e.toMonoidHom hxPED
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xE, hxPE, rfl⟩
    have hxPE' : xE ∈ (PED : Subgroup ED).map e.toMonoidHom := by
      simpa [PE] using hxPE
    rcases Subgroup.mem_map.mp hxPE' with ⟨xED, hxPED, hx⟩
    change (xED : D) ∈ (PD : Subgroup D) at hxPED
    rw [hP]
    apply Subgroup.mem_map.mpr
    refine ⟨xED, hxPED, ?_⟩
    exact congrArg Subtype.val hx

/-- Cardinality of a disjoint subgroup product when the right factor
normalizes the left. -/
private theorem lemma101_natCard_sup_eq_mul
    {G : Type*} [Group G] (A B : Subgroup G)
    (hnorm : B ≤ Subgroup.normalizer (A : Set G))
    (hdisj : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G),
      Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have hinj : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective toSup := by
    intro x
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnorm]
      exact x.property
    rcases hx with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinj, hsurj⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

/-- Once `(10B)` is known, the first Corollary 8.5 factor is exactly the
`p'`-core of `V`. -/
public theorem Lemma101ChoiceData.A1_eq_pPrimeCore
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (hPsylD : theorem4bIsSylowSubgroupOf d.p d.P D) :
    d.initial.A1 =
      (pPrimeCore d.p (peterfalviV D t)).map
        (peterfalviV D t).subtype := by
  classical
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.initial.A1
  let P : Subgroup X := d.P
  let O : Subgroup X := (pPrimeCore d.p V).map V.subtype
  letI : Fact d.p.Prime := ⟨d.p_prime⟩
  have hAV : A ≤ V := by
    dsimp [A, V]
    rw [d.initial.A1_eq]
    exact inf_le_left
  have hPV : P ≤ V := d.P_le_V
  have hVD : V ≤ D := inf_le_left
  have hPsylV : theorem4bIsSylowSubgroupOf d.p P V :=
    theorem4bIsSylowSubgroupOf_of_between d.p_prime hPsylD hPV hVD
  have hPnormA : P ≤ Subgroup.normalizer (A : Set X) :=
    hPV.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hAV).mp
      d.initial.A1_normal_V)
  have hVsup : A ⊔ P = V := by
    apply le_antisymm
    · exact sup_le hAV hPV
    · intro x hxV
      have hxprod : x ∈ (A : Set X) * (P : Set X) := by
        rw [← d.initial.V_eq_mul]
        exact hxV
      rcases Set.mem_mul.mp hxprod with ⟨a, ha, p, hp, hap⟩
      rw [← hap]
      exact Subgroup.mul_mem_sup ha hp
  have hcardV : Nat.card V = Nat.card A * d.p := by
    rw [← hVsup, lemma101_natCard_sup_eq_mul A P hPnormA
      d.initial.A1_disjoint_P, d.card_P_eq]
  have hcopA : Nat.Coprime d.p (Nat.card A) := by
    rw [d.p_prime.coprime_iff_not_dvd]
    intro hpA
    rcases hpA with ⟨k, hk⟩
    have hp2V : d.p ^ 2 ∣ Nat.card V := by
      refine ⟨k, ?_⟩
      rw [hcardV, hk]
      ring
    rcases hPsylV with ⟨PV, hPmap⟩
    have hp2PV : d.p ^ 2 ∣ Nat.card (PV : Subgroup V) :=
      PV.pow_dvd_card_of_pow_dvd_card hp2V
    have hcardPV : Nat.card (PV : Subgroup V) = d.p := by
      calc
        Nat.card (PV : Subgroup V) = Nat.card P := by
          rw [hPmap]
          exact (Subgroup.card_map_of_injective V.subtype_injective).symm
        _ = d.p := d.card_P_eq
    have hp2p : d.p ^ 2 ∣ d.p := by simpa [hcardPV] using hp2PV
    have hpOne : d.p ∣ 1 := by
      apply Nat.dvd_of_mul_dvd_mul_right d.p_prime.pos
      simpa [pow_two] using hp2p
    exact d.p_prime.not_dvd_one hpOne
  have hAleO : A ≤ O := by
    letI : (A.subgroupOf V).Normal := d.initial.A1_normal_V
    exact subgroupOf_le_pPrimeCore_map hAV hcopA
  have hOcop : Nat.Coprime d.p (Nat.card O) := by
    have hcardO : Nat.card O = Nat.card (pPrimeCore d.p V) :=
      Subgroup.card_map_of_injective V.subtype_injective
    rw [hcardO]
    exact pPrimeCore_coprime_card
  have hPdisjO : Disjoint P O := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [d.card_P_eq]
    exact hOcop
  apply le_antisymm
  · exact hAleO
  · intro x hxO
    have hxV : x ∈ V := (Subgroup.map_subtype_le (pPrimeCore d.p V)) hxO
    have hxprod : x ∈ (A : Set X) * (P : Set X) := by
      rw [← d.initial.V_eq_mul]
      exact hxV
    rcases Set.mem_mul.mp hxprod with ⟨a, ha, p, hp, hap⟩
    have haO : a ∈ O := hAleO ha
    have hpO : p ∈ O := by
      have hpEq : p = a⁻¹ * x := by
        calc
          p = a⁻¹ * (a * p) := by simp
          _ = a⁻¹ * x := by rw [hap]
      rw [hpEq]
      exact O.mul_mem (O.inv_mem haO) hxO
    have hpOne : p = 1 :=
      Subgroup.disjoint_def.mp hPdisjO hp hpO
    have hxEq : x = a := by
      calc
        x = a * p := hap.symm
        _ = a := by rw [hpOne]; simp
    rwa [hxEq]

/-- The chosen prime-order factor misses the ambient derived subgroup.  This
is the checked algebraic part of source `(10B)`: it uses only the Peterfalvi
decomposition, the initial `V = A₁ P` package, and the coprimality conclusion
of `[II1; 4.3(a)]`. -/
public theorem Lemma101ChoiceData.inf_derived_D_eq_bot
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hcop : Nat.Coprime d.p
      (Nat.card (Subgroup.closure (peterfalviKSet D t)))) :
    d.P ⊓ (derivedSubgroup D).map D.subtype = ⊥ := by
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.initial.A1
  let P : Subgroup X := d.P
  let N : Subgroup X := K ⊔ A
  have hKD : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hVD : V ≤ D := inf_le_left
  have hAV : A ≤ V := by
    dsimp [A, V]
    rw [d.initial.A1_eq]
    exact inf_le_left
  have hPV : P ≤ V := d.P_le_V
  have hAD : A ≤ D := hAV.trans hVD
  have hPD : P ≤ D := hPV.trans hVD
  have hVsup : A ⊔ P = V := by
    apply le_antisymm
    · exact sup_le hAV hPV
    · intro x hxV
      have hxprod : x ∈ (A : Set X) * (P : Set X) := by
        rw [← d.initial.V_eq_mul]
        exact hxV
      rw [Set.mem_mul] at hxprod
      rcases hxprod with ⟨a, ha, p, hp, hap⟩
      rw [← hap]
      exact Subgroup.mul_mem_sup ha hp
  have hDsup : K ⊔ V = D := by
    simpa [K, V] using
      lemma101_peterfalviKernel_sup_fixed_eq ht hDodd hDnorm
  have hKnormal : (K.subgroupOf D).Normal := by
    simpa [K] using lemma101_peterfalviKernel_normal ht hDodd hDnorm
  have hKinfV : K ⊓ V ≤ A := by
    exact lemma101_inf_le_complement_of_coprime
      hAV hPV d.initial.A1_normal_V hVsup d.initial.A1_disjoint_P
        d.card_P_eq (by simpa [K] using hcop)
  have hND : N ≤ D := sup_le hKD hAD
  have hKnormN : K ≤ Subgroup.normalizer (N : Set X) :=
    (show K ≤ N from le_sup_left).trans Subgroup.le_normalizer
  have hVnormK : V ≤ Subgroup.normalizer (K : Set X) := by
    exact hVD.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKD).mp hKnormal)
  have hVnormA : V ≤ Subgroup.normalizer (A : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAV).mp
      d.initial.A1_normal_V
  have hVnormN : V ≤ Subgroup.normalizer (N : Set X) := by
    simpa [N] using lemma101_le_normalizer_sup_of_normalizes hVnormK hVnormA
  have hDnormN : D ≤ Subgroup.normalizer (N : Set X) := by
    rw [← hDsup]
    exact sup_le hKnormN hVnormN
  have hNnormal : (N.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hND).mpr hDnormN
  have hNsupP : N ⊔ P = D := by
    calc
      N ⊔ P = K ⊔ (A ⊔ P) := by simp [N, sup_assoc]
      _ = K ⊔ V := by rw [hVsup]
      _ = D := hDsup
  have hPdisjN : Disjoint P N := by
    rw [Subgroup.disjoint_def]
    intro x hxP hxN
    let KD : Subgroup D := K.subgroupOf D
    let AD : Subgroup D := A.subgroupOf D
    let ND : Subgroup D := N.subgroupOf D
    let xD : D := ⟨x, hPD hxP⟩
    letI : KD.Normal := by simpa [KD] using hKnormal
    have hND_eq : ND = KD ⊔ AD := by
      simpa [ND, KD, AD, N] using Subgroup.subgroupOf_sup hKD hAD
    have hmulD : (ND : Set D) = (KD : Set D) * (AD : Set D) := by
      rw [hND_eq, Subgroup.normal_mul]
    have hxprod : xD ∈ (KD : Set D) * (AD : Set D) := by
      rw [← hmulD]
      exact hxN
    rw [Set.mem_mul] at hxprod
    rcases hxprod with ⟨k, hkK, a, haA, hka⟩
    have hkV : (k : X) ∈ V := by
      have hkaX : (k : X) * (a : X) = x := congrArg Subtype.val hka
      have hkEq : (k : X) = x * (a : X)⁻¹ := by
        calc
          (k : X) = (k : X) * (a : X) * (a : X)⁻¹ := by simp [mul_assoc]
          _ = x * (a : X)⁻¹ := by rw [hkaX]
      rw [hkEq]
      exact V.mul_mem (hPV hxP) (V.inv_mem (hAV haA))
    have hkA : (k : X) ∈ A := hKinfV ⟨hkK, hkV⟩
    have hxA : x ∈ A := by
      have hkaX : (k : X) * (a : X) = x := congrArg Subtype.val hka
      rw [← hkaX]
      exact A.mul_mem hkA haA
    exact Subgroup.disjoint_def.mp d.initial.A1_disjoint_P hxA hxP
  let ND : Subgroup D := N.subgroupOf D
  let PD : Subgroup D := P.subgroupOf D
  have hNtop : ND ⊔ PD = ⊤ := by
    calc
      ND ⊔ PD = (N ⊔ P).subgroupOf D := by
        simpa [ND, PD] using (Subgroup.subgroupOf_sup hND hPD).symm
      _ = D.subgroupOf D := by rw [hNsupP]
      _ = ⊤ := Subgroup.subgroupOf_self D
  have hPDcard : Nat.card PD = d.p := by
    calc
      Nat.card PD = Nat.card P := natCard_subgroupOf_eq P D hPD
      _ = d.p := d.card_P_eq
  letI : Fact d.p.Prime := ⟨d.p_prime⟩
  have hPDcomm : IsMulCommutative PD :=
    ⟨(isCyclic_of_prime_card hPDcard).isMulCommutative.is_comm⟩
  have hcommSub : commutator D ≤ ND := by
    have hNnormal' : ND.Normal := by simpa [ND] using hNnormal
    exact hNnormal'.commutator_le_of_self_sup_commutative_eq_top hNtop hPDcomm
  have hcommAmb : (commutator D).map D.subtype ≤ N := by
    calc
      (commutator D).map D.subtype ≤ ND.map D.subtype :=
        Subgroup.map_mono hcommSub
      _ = N := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hND]
  rw [eq_bot_iff]
  intro x hx
  have hxComm : x ∈ (commutator D).map D.subtype := by
    simpa [derivedSubgroup, commutator] using hx.2
  exact Subgroup.disjoint_def.mp hPdisjN hx.1 (hcommAmb hxComm)

/-! The next helper is the uniform Corollary 8.5 application in the source
proof.  It is stated for an arbitrary nontrivial `P`-invariant subgroup of
`A₁`; no later part of Lemma 10.1 is used. -/

public theorem Lemma101ChoiceData.corollary85_supported_of_nontrivial_invariant
    {X : Type u} [Group X] [Finite X]
    {M E : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101ChoiceData
      (M ⊓ rightConjugate M t) E
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    {B : Subgroup X}
    (hBA1 : B ≤ d.initial.A1)
    (hBne : B ≠ ⊥)
    (hPnormB : d.P ≤ Subgroup.normalizer (B : Set X)) :
    Nonempty (Corollary85SupportedConclusion M t d83.u B d.P) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  have hA1V : d.initial.A1 ≤ V := by
    rw [d.initial.A1_eq]
    exact inf_le_left
  have hBV : B ≤ V := hBA1.trans hA1V
  have hVeq : V = D ⊓ Subgroup.centralizer ({d83.u} : Set X) := by
    simpa [D, V, peterfalviV] using d83.centralizer_eq
  have hBlocal :
      B ≤ (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X) := by
    simpa [D, ← hVeq] using hBV
  have hPlocal : d.P ≤ normalizerIn
      ((M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X)) B := by
    intro p hp
    exact ⟨by simpa [D, ← hVeq] using d.P_le_V hp, hPnormB hp⟩
  obtain ⟨j, hjI, hjCY, hjne⟩ := d.Y_nontrivial_centralizer
  have hjJ : j ∈ d.initial.J := by
    change j ∈ (d.initial.J : Set X)
    rw [d.initial.J_eq_centralizer]
    exact ⟨hjI, hjCY⟩
  have hjCB : j ∈ Subgroup.centralizer (B : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hbB
    have hbA1 := hBA1 hbB
    rw [d.initial.A1_eq] at hbA1
    exact (Subgroup.mem_centralizer_iff.mp hbA1.2 j hjJ).symm
  have hInormalizer : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t B := by
    exact ⟨j, hjI, centralizer_le_normalizer B hjCB, hjne⟩
  have hPne : d.P ≠ ⊥ := by
    intro hPbot
    exact d.initial.card_P_prime.ne_one (by simp [hPbot])
  have hfixed : Corollary85FixedPointFree
      (M ⊓ rightConjugate M t) t B d.P := by
    intro g hgP hgne k hkI _hkN hcomm
    exact d.P_fixedPointFree g hgP hgne k hkI hcomm
  exact h84.corollary85_supported
    d83 hM ht htM hBlocal hBne hInormalizer hPlocal hPne hfixed

/-- Project the source-facing Corollary 8.5 conclusion from the retained
proof-support package. -/
public theorem Lemma101ChoiceData.corollary85_of_nontrivial_invariant
    {X : Type u} [Group X] [Finite X]
    {M E : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101ChoiceData
      (M ⊓ rightConjugate M t) E
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    {B : Subgroup X}
    (hBA1 : B ≤ d.initial.A1)
    (hBne : B ≠ ⊥)
    (hPnormB : d.P ≤ Subgroup.normalizer (B : Set X)) :
    Nonempty (Corollary85Conclusion M t d83.u B d.P) := by
  obtain ⟨supported⟩ := d.corollary85_supported_of_nontrivial_invariant
    hM ht htM d83 h84 hBA1 hBne hPnormB
  exact ⟨supported.conclusion⟩

/-- Uniform centralizer count supplied by Corollary 8.5 for every nontrivial
`P`-invariant subgroup of `A₁`.  The witness is the subgroup denoted
`C_I(B)` in the source. -/
public theorem Lemma101ChoiceData.exists_centralizer_card_of_nontrivial_invariant
    {X : Type u} [Group X] [Finite X]
    {M E : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101ChoiceData
      (M ⊓ rightConjugate M t) E
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    {B : Subgroup X}
    (hBA1 : B ≤ d.initial.A1)
    (hBne : B ≠ ⊥)
    (hPnormB : d.P ≤ Subgroup.normalizer (B : Set X)) :
    ∃ J : Subgroup X,
      (J : Set X) =
          {x : X |
            x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
              x ∈ Subgroup.centralizer (B : Set X)} ∧
        Nat.card J = 2 ^ d.p - 1 := by
  obtain ⟨h85⟩ := d.corollary85_of_nontrivial_invariant
    hM ht htM d83 h84 hBA1 hBne hPnormB
  exact ⟨h85.J, h85.J_eq_centralizer, by
    simpa [d.card_P_eq] using h85.J_card⟩

/-- The uniform Corollary 8.5 cardinality upgrades to equality of the
Peterfalvi centralizers: `C_I(B) = C_I(A₁)` for every nontrivial
`P`-invariant subgroup `B ≤ A₁`. -/
public theorem Lemma101ChoiceData.centralizer_uniform
    {X : Type u} [Group X] [Finite X]
    {M E : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101ChoiceData
      (M ⊓ rightConjugate M t) E
      (peterfalviV (M ⊓ rightConjugate M t) t) t) :
    (d.initial.J : Set X) =
        {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
          x ∈ Subgroup.centralizer (d.initial.A1 : Set X)} ∧
      ∀ (B : Subgroup X), B ≤ d.initial.A1 → B ≠ ⊥ →
        d.P ≤ Subgroup.normalizer (B : Set X) →
        ∃ J : Subgroup X,
          (J : Set X) =
            {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
              x ∈ Subgroup.centralizer (B : Set X)} ∧
          J = d.initial.J := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  have hA1V : d.initial.A1 ≤ V := by
    rw [d.initial.A1_eq]
    exact inf_le_left
  have hPnormA : d.P ≤ Subgroup.normalizer (d.initial.A1 : Set X) := by
    intro p hp
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hA1V).mp
      d.initial.A1_normal_V (d.P_le_V hp)
  obtain ⟨h85A⟩ := d.corollary85_of_nontrivial_invariant
    hM ht htM d83 h84 le_rfl d.initial.A1_ne_bot hPnormA
  have hJAlE : h85A.J ≤ d.initial.J := by
    intro x hx
    change x ∈ (h85A.J : Set X) at hx
    rw [h85A.J_eq_centralizer] at hx
    change x ∈ (d.initial.J : Set X)
    rw [d.initial.J_eq_centralizer]
    refine ⟨hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hyY
    exact (Subgroup.mem_centralizer_iff.mp hx.2 y
      (d.initial.Y_le_A1 hyY))
  have hJAeq : h85A.J = d.initial.J := by
    apply Subgroup.eq_of_le_of_card_ge hJAlE
    rw [h85A.J_card, d.initial.J_card]
  have hJsetA : (d.initial.J : Set X) =
      {x : X | x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (d.initial.A1 : Set X)} := by
    rw [← hJAeq]
    simpa [D] using h85A.J_eq_centralizer
  refine ⟨hJsetA, ?_⟩
  intro B hBA hBne hPnormB
  obtain ⟨h85B⟩ := d.corollary85_of_nontrivial_invariant
    hM ht htM d83 h84 hBA hBne hPnormB
  have hJleB : d.initial.J ≤ h85B.J := by
    intro x hx
    change x ∈ (d.initial.J : Set X) at hx
    rw [hJsetA] at hx
    change x ∈ (h85B.J : Set X)
    rw [h85B.J_eq_centralizer]
    refine ⟨hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp hx.2 b (hBA hb))
  have hJeqB : d.initial.J = h85B.J := by
    apply Subgroup.eq_of_le_of_card_ge hJleB
    rw [h85B.J_card, d.initial.J_card]
  refine ⟨h85B.J, h85B.J_eq_centralizer, ?_⟩
  exact hJeqB.symm

/-- Construct the initial Lemma 10.1 choice package from Corollary 9.5,
Proposition 9.3, and the source-facing Corollary 8.5 endpoint. -/
public theorem lemma101_exists_choice_data
    {X : Type u} [Group X] [Finite X]
    {M E : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hEodd : Odd (Nat.card E)) (hEne : E ≠ ⊥)
    (h95 : ∀ p : ℕ, Nat.Prime p →
      p ∣ Nat.card (E ⧸ derivedSubgroup E) →
      Lemma94AlternativeB (M ⊓ rightConjugate M t) E t p)
    (h93 : Proposition93Conclusion
      (M ⊓ rightConjugate M t) E t) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    let V : Subgroup X := peterfalviV D t
    Nonempty (Lemma101ChoiceData D E V t) := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  letI : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
  obtain ⟨p, hp, hpAb⟩ := lemma99_exists_prime_dvd_abelianization hEodd
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hScyclic, hSV, hStrivial⟩ := h95 p hp hpAb
  let P : Subgroup X := (S : Subgroup E).map E.subtype
  have hPV : P ≤ V := by simpa [D, V, P] using hSV
  have hpE : p ∣ Nat.card E :=
    hpAb.trans (Subgroup.card_quotient_dvd_card
      (s := derivedSubgroup E))
  have hpS : p ∣ Nat.card (S : Subgroup E) :=
    S.dvd_card_of_dvd_card hpE
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hSbot : (S : Subgroup E) = ⊥ :=
      Subgroup.map_injective E.subtype_injective
        (by simpa [P] using hPbot)
    have hpOne : p ∣ 1 := by simpa [hSbot] using hpS
    exact hp.ne_one (Nat.dvd_one.mp hpOne)
  have h93exists := h93.exists_normal_with_nontrivial_centralizer
  change ∃ Y : Subgroup X,
    Y ≤ V ∧ Y ≠ ⊥ ∧ (Y.subgroupOf V).Normal ∧
      HasNontrivialPeterfalviCentralizer D t Y at h93exists
  obtain ⟨Y, hYV, hYne, hYnormal, hYcentral⟩ := h93exists
  have hD : D = M ⊓ rightConjugate M t := rfl
  have hVeq : V = D ⊓ Subgroup.centralizer ({d83.u} : Set X) := by
    simpa [D, V, peterfalviV] using d83.centralizer_eq
  have hYlocal : Y ≤ D ⊓ Subgroup.centralizer ({d83.u} : Set X) := by
    rw [← hVeq]
    exact hYV
  have hInormalizer : HasNontrivialPeterfalviNormalizer D t Y := by
    obtain ⟨j, hjI, hjC, hjne⟩ := hYcentral
    exact ⟨j, hjI, centralizer_le_normalizer Y hjC, hjne⟩
  have hNlocal :
      normalizerIn (D ⊓ Subgroup.centralizer ({d83.u} : Set X)) Y = V := by
    rw [← hVeq]
    exact normalizerIn_eq_self_of_le_of_normal hYV hYnormal
  have hPVlocal : P ≤
      normalizerIn (D ⊓ Subgroup.centralizer ({d83.u} : Set X)) Y := by
    rw [hNlocal]
    exact hPV
  have hfixed : Corollary85FixedPointFree D t Y P := by
    intro g hgP hgne j hjI _hjN hcomm
    exact hStrivial g (by simpa [P] using hgP) hgne j hjI hcomm
  obtain ⟨h85⟩ :=
    Proposition84Statement.corollary85
      d83 h84 hM ht htM (by simpa [D] using hYlocal) hYne
      (by simpa [D] using hInormalizer)
      (by simpa [D] using hPVlocal) hPne
      (by simpa [D] using hfixed)
  obtain ⟨hinit⟩ :=
    lemma101_initial_data_of_corollary85 hD hVeq le_rfl hYV hYne hYnormal
      hYcentral hPV (by simpa [D, P] using hStrivial) h85
  exact ⟨{
    p := p
    p_prime := hp
    p_dvd_abelianization := hpAb
    S := S
    P := P
    P_eq_map := rfl
    S_cyclic := hScyclic
    P_le_V := hPV
    P_fixedPointFree := by simpa [D, P] using hStrivial
    Y := Y
    Y_le_V := hYV
    Y_ne_bot := hYne
    Y_normal_V := hYnormal
    Y_nontrivial_centralizer := hYcentral
    initial := hinit }⟩

/-- The source `(10B)` contradiction after Lemma 9.4 has produced its
fusion-control alternative.  Minimality and the focal equality force a
nontrivial element of `P` into the already-trivial intersection `P ∩ D'`. -/
public theorem false_of_lemma94AlternativeA
    {X : Type u} [Group X] [Finite X]
    {M D W P : Subgroup X} {p : ℕ} [Fact p.Prime]
    (hW : IsMinimalNormalSupplement M D W)
    (hDle : D ≤ M)
    (hPW : P ≤ W)
    (hPD : P ≤ D)
    (hPp : IsPGroup p P)
    (hPne : P ≠ ⊥)
    (hPinfD : P ⊓ (commutator D).map D.subtype = ⊥)
    (Q : Sylow p M)
    (hQD : (Q : Subgroup M) ≤ D.subgroupOf M)
    (hfusion : ControlsFusionIn (D.subgroupOf M) (Q : Subgroup M)) :
    False := by
  classical
  have hres : External.hallPResidual p W = ⊤ :=
    hallPResidual_eq_top_of_minimalNormalSupplement hW Q hQD
  let PW : Subgroup W := P.subgroupOf W
  have hPWp : IsPGroup p PW :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPW).symm
  have hPWcomm : PW ≤ commutator W :=
    isPGroup_le_commutator_of_hallPResidual_eq_top hPWp hres
  have hPcommM : P ≤ (commutator M).map M.subtype := by
    intro x hxP
    have hxW : (⟨x, hPW hxP⟩ : W) ∈ PW := hxP
    have hxcommW : (⟨x, hPW hxP⟩ : W) ∈ commutator W :=
      hPWcomm hxW
    have hxmapW : x ∈ (commutator W).map W.subtype :=
      Subgroup.mem_map_of_mem W.subtype hxcommW
    rw [Subgroup.map_subtype_commutator] at hxmapW
    have hxcommM : x ∈ ⁅M, M⁆ :=
      Subgroup.commutator_mono hW.prop.le_M hW.prop.le_M hxmapW
    rw [Subgroup.map_subtype_commutator]
    exact hxcommM
  let DM : Subgroup M := D.subgroupOf M
  let PM : Subgroup M := P.subgroupOf M
  have hPMDM : PM ≤ DM := by
    intro x hx
    exact hPD hx
  have hPMp : IsPGroup p PM :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe
      (hPD.trans hDle)).symm
  have hfocal : PM ⊓ commutator M =
      PM ⊓ (commutator DM).map DM.subtype :=
    inf_commutator_eq_of_controlsFusionIn_of_isPGroup
      DM PM Q hQD hPMDM hPMp hfusion
  obtain ⟨xP, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  let x : X := xP
  have hxP : x ∈ P := xP.property
  let xM : M := ⟨x, hDle (hPD hxP)⟩
  have hxcommMmap : x ∈ (commutator M).map M.subtype := hPcommM hxP
  rcases Subgroup.mem_map.mp hxcommMmap with ⟨y, hycomm, hyx⟩
  have hyEq : y = xM := Subtype.ext hyx
  have hxMcomm : xM ∈ commutator M := by simpa [hyEq] using hycomm
  have hxMinf : xM ∈ PM ⊓ commutator M := ⟨hxP, hxMcomm⟩
  have hxMinfD : xM ∈ PM ⊓ (commutator DM).map DM.subtype := by
    rw [← hfocal]
    exact hxMinf
  have hxNested : x ∈
      ((commutator DM).map DM.subtype).map M.subtype :=
    Subgroup.mem_map_of_mem M.subtype hxMinfD.2
  have hmapcomm :
      ((commutator DM).map DM.subtype).map M.subtype =
        (commutator D).map D.subtype := by
    simpa [DM] using
      (show
        ((commutator (D.subgroupOf M)).map
            (D.subgroupOf M).subtype).map M.subtype =
          (commutator D).map D.subtype by
        rw [Subgroup.map_subtype_commutator,
          Subgroup.map_commutator, Subgroup.map_subtype_commutator]
        rw [show (D.subgroupOf M).map M.subtype = D by
          rw [Subgroup.subgroupOf_map_subtype]
          exact inf_eq_left.mpr hDle])
  have hxcommD : x ∈ (commutator D).map D.subtype := by
    rw [← hmapcomm]
    exact hxNested
  have hxbot : x ∈ (⊥ : Subgroup X) := by
    rw [← hPinfD]
    exact ⟨hxP, hxcommD⟩
  exact hxne (by simpa [x] using hxbot)

/-- A cyclic `p`-subgroup cannot properly enlarge the right factor of an
internal direct product when that factor has order `p`. -/
public theorem eq_right_of_cyclic_isPGroup_of_internalDirectProduct
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {N C P R : Subgroup G}
    (hprod : Section2.IsInternalDirectProduct N C P)
    (hRN : R ≤ N)
    (hPR : P ≤ R)
    (hRp : IsPGroup p R)
    (hRcyclic : IsCyclic R)
    (hPcard : Nat.card P = p) :
    R = P := by
  classical
  let CR : Subgroup G := C ⊓ R
  have hCRp : IsPGroup p CR := by
    let CRR : Subgroup R := CR.subgroupOf R
    have hCRRp : IsPGroup p CRR := hRp.to_subgroup CRR
    exact hCRRp.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right)
  have hprodR : Section2.IsInternalDirectProduct R CR P := by
    refine {
      left_le := inf_le_right
      right_le := hPR
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
    · intro c hc p hp
      exact hprod.commute c hc.1 p hp
    · rw [eq_bot_iff]
      intro x hx
      have hxCP : x ∈ C ⊓ P := ⟨hx.1.1, hx.2⟩
      rw [hprod.inf_eq_bot] at hxCP
      exact hxCP
    · intro r hr
      obtain ⟨c, hc, q, hq, hrEq⟩ := hprod.mul_surjective r (hRN hr)
      have hcR : c ∈ R := by
        have hcEq : c = r * q⁻¹ := by
          rw [hrEq]
          simp [mul_assoc]
        rw [hcEq]
        exact R.mul_mem hr (R.inv_mem (hPR hq))
      exact ⟨c, ⟨hc, hcR⟩, q, hq, hrEq⟩
  let e : CR × P ≃* R := Section3.internalDirectProductMulEquiv hprodR
  have hprodCyclic : IsCyclic (CR × P) := e.isCyclic.mpr hRcyclic
  letI : IsCyclic (CR × P) := hprodCyclic
  have hcop : Nat.Coprime (Nat.card CR) (Nat.card P) :=
    coprime_card_of_isCyclic_prod CR P
  rw [hPcard] at hcop
  have hCRcard : Nat.card CR = 1 := by
    rcases hCRp.card_eq_or_dvd with hcard | hpdiv
    · exact hcard
    · exact False.elim
        ((Fact.out : Nat.Prime p).ne_one (hcop.symm.eq_one_of_dvd hpdiv))
  have hCRbot : CR = ⊥ := Subgroup.card_eq_one.mp hCRcard
  apply le_antisymm
  · intro r hr
    obtain ⟨c, hc, q, hq, hrEq⟩ := hprodR.mul_surjective r hr
    have hcOne : c = 1 := by
      have hcBot : c ∈ (⊥ : Subgroup G) := by simpa [hCRbot] using hc
      simpa using hcBot
    simpa [hrEq, hcOne] using hq
  · exact hPR

/-- The factorization `V = A P`, normality of `A`, and `A ∩ P = 1` make
`P` a direct factor of its normalizer in `V`. -/
public theorem normalizer_internalDirectProduct_of_mul_eq
    {G : Type*} [Group G] [Finite G]
    {V A P N : Subgroup G}
    (hAV : A ≤ V)
    (hPV : P ≤ V)
    (hAnormal : (A.subgroupOf V).Normal)
    (hVmul : (V : Set G) = (A : Set G) * (P : Set G))
    (hdisj : Disjoint A P)
    (hN : N = normalizerIn V P) :
    Section2.IsInternalDirectProduct N
      (A ⊓ Subgroup.centralizer (P : Set G)) P := by
  classical
  let C : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G)
  have hVnormA : V ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAV).mp hAnormal
  refine {
    left_le := ?_
    right_le := ?_
    commute := ?_
    inf_eq_bot := ?_
    mul_surjective := ?_ }
  · intro c hc
    rw [hN]
    exact ⟨hAV hc.1, centralizer_le_normalizer P hc.2⟩
  · intro p hp
    rw [hN]
    exact ⟨hPV hp, Subgroup.le_normalizer hp⟩
  · intro c hc p hp
    exact (Subgroup.mem_centralizer_iff.mp hc.2 p hp).symm
  · rw [eq_bot_iff]
    intro x hx
    exact Subgroup.disjoint_def.mp hdisj hx.1.1 hx.2
  · intro n hn
    have hnV : n ∈ V := by
      rw [hN] at hn
      exact hn.1
    have hnNormP : n ∈ Subgroup.normalizer (P : Set G) := by
      rw [hN] at hn
      exact hn.2
    have hnProd : n ∈ (A : Set G) * (P : Set G) := by
      rw [← hVmul]
      exact hnV
    rcases Set.mem_mul.mp hnProd with ⟨a, ha, p, hp, hap⟩
    have haEq : a = n * p⁻¹ := by
      rw [← hap]
      simp [mul_assoc]
    have haNormP : a ∈ Subgroup.normalizer (P : Set G) := by
      rw [haEq]
      exact (Subgroup.normalizer (P : Set G)).mul_mem hnNormP
        ((Subgroup.normalizer (P : Set G)).inv_mem
          (Subgroup.le_normalizer hp))
    have haCentral : a ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have haqP : a * q * a⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp haNormP q).mp hq
      have hcommP : a * q * a⁻¹ * q⁻¹ ∈ P :=
        P.mul_mem haqP (P.inv_mem hq)
      have hqNormA : q ∈ Subgroup.normalizer (A : Set G) :=
        hVnormA (hPV hq)
      have hqAinv : q * a⁻¹ * q⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hqNormA a⁻¹).mp (A.inv_mem ha)
      have hcommA : a * q * a⁻¹ * q⁻¹ ∈ A := by
        simpa [mul_assoc] using A.mul_mem ha hqAinv
      have hcommOne : a * q * a⁻¹ * q⁻¹ = 1 :=
        Subgroup.disjoint_def.mp hdisj hcommA hcommP
      have haq : a * q = q * a := by
        calc
          a * q = (a * q * a⁻¹ * q⁻¹) * (q * a) := by group
          _ = q * a := by rw [hcommOne]; simp
      exact haq.symm
    exact ⟨a, ⟨ha, haCentral⟩, p, hp, hap.symm⟩

/-- An internal direct-product package gives the subgroup join equality. -/
public theorem internalDirectProduct_eq_sup
    {G : Type*} [Group G]
    {N C P : Subgroup G}
    (hprod : Section2.IsInternalDirectProduct N C P) :
    N = C ⊔ P := by
  apply le_antisymm
  · intro x hx
    rcases hprod.mul_surjective x hx with ⟨c, hc, p, hp, hxp⟩
    rw [hxp]
    exact Subgroup.mul_mem_sup hc hp
  · exact sup_le hprod.left_le hprod.right_le

/-- An internal direct-product package gives the corresponding set product. -/
public theorem internalDirectProduct_coe_eq_mul
    {G : Type*} [Group G]
    {N C P : Subgroup G}
    (hprod : Section2.IsInternalDirectProduct N C P) :
    (N : Set G) = (C : Set G) * (P : Set G) := by
  ext x
  constructor
  · intro hx
    rcases hprod.mul_surjective x hx with ⟨c, hc, p, hp, hxp⟩
    exact Set.mem_mul.mpr ⟨c, hc, p, hp, hxp.symm⟩
  · rintro ⟨c, hc, p, hp, rfl⟩
    exact N.mul_mem (hprod.left_le hc) (hprod.right_le hp)

/-- The factors in an internal direct product are disjoint. -/
public theorem internalDirectProduct_disjoint
    {G : Type*} [Group G]
    {N C P : Subgroup G}
    (hprod : Section2.IsInternalDirectProduct N C P) :
    Disjoint C P := by
  rw [disjoint_iff]
  exact hprod.inf_eq_bot

/-- Specialization of the checked normalizer direct-product theorem to the
choices made in Lemma 10.1. -/
public theorem Lemma101ChoiceData.normalizer_internalDirectProduct
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (hNormEq : normalizerIn D d.P =
      normalizerIn (peterfalviV D t) d.P) :
    Section2.IsInternalDirectProduct
      (normalizerIn D d.P)
      (d.initial.A1 ⊓ Subgroup.centralizer (d.P : Set X)) d.P := by
  have hA_V : d.initial.A1 ≤ peterfalviV D t := by
    rw [d.initial.A1_eq]
    exact inf_le_left
  exact normalizer_internalDirectProduct_of_mul_eq
    hA_V d.P_le_V d.initial.A1_normal_V d.initial.V_eq_mul
      d.initial.A1_disjoint_P hNormEq

/-- The join, set-product, and disjointness forms of the normalizer
factorization in Lemma 10.1(c). -/
public theorem Lemma101ChoiceData.normalizer_factorization
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (hNormEq : normalizerIn D d.P =
      normalizerIn (peterfalviV D t) d.P) :
    normalizerIn D d.P =
        (d.initial.A1 ⊓ Subgroup.centralizer (d.P : Set X)) ⊔ d.P ∧
      (normalizerIn D d.P : Set X) =
        ((d.initial.A1 ⊓ Subgroup.centralizer (d.P : Set X)) : Set X) *
          (d.P : Set X) ∧
      Disjoint
        (d.initial.A1 ⊓ Subgroup.centralizer (d.P : Set X)) d.P := by
  have hprod := d.normalizer_internalDirectProduct hNormEq
  exact ⟨internalDirectProduct_eq_sup hprod,
    internalDirectProduct_coe_eq_mul hprod,
    internalDirectProduct_disjoint hprod⟩

/-- The Peterfalvi decomposition `D = K V` and the initial factorization
`V = A₁ P` give the source-ordered product `D = K A₁ P`. -/
public theorem Lemma101ChoiceData.D_eq_kernel_mul_A1_mul_P
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X)) :
    (D : Set X) =
      (Subgroup.closure (peterfalviKSet D t) : Set X) *
        (d.initial.A1 : Set X) * (d.P : Set X) := by
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.initial.A1
  let P : Subgroup X := d.P
  have hKD : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hVD : V ≤ D := inf_le_left
  have hAV : A ≤ V := by
    dsimp [A, V]
    rw [d.initial.A1_eq]
    exact inf_le_left
  have hAD : A ≤ D := hAV.trans hVD
  have hPD : P ≤ D := d.P_le_V.trans hVD
  have hKV : K ⊔ V = D := by
    simpa [K, V] using
      lemma101_peterfalviKernel_sup_fixed_eq ht hDodd hDnorm
  have hKnormal : (K.subgroupOf D).Normal := by
    simpa [K] using lemma101_peterfalviKernel_normal ht hDodd hDnorm
  let KD : Subgroup D := K.subgroupOf D
  let VD : Subgroup D := V.subgroupOf D
  have htop : KD ⊔ VD = ⊤ := by
    calc
      KD ⊔ VD = (K ⊔ V).subgroupOf D := by
        simpa [KD, VD] using (Subgroup.subgroupOf_sup hKD hVD).symm
      _ = D.subgroupOf D := by rw [hKV]
      _ = ⊤ := Subgroup.subgroupOf_self D
  letI : KD.Normal := by simpa [KD] using hKnormal
  ext x
  constructor
  · intro hxD
    let xD : D := ⟨x, hxD⟩
    have hxKV : xD ∈ (KD : Set D) * (VD : Set D) := by
      rw [← Subgroup.normal_mul KD VD, htop]
      trivial
    rcases Set.mem_mul.mp hxKV with ⟨k, hk, v, hv, hkv⟩
    have hvProd : (v : X) ∈ (A : Set X) * (P : Set X) := by
      rw [← d.initial.V_eq_mul]
      exact hv
    rcases Set.mem_mul.mp hvProd with ⟨a, ha, p, hp, hap⟩
    apply Set.mem_mul.mpr
    refine ⟨(k : X) * a, ?_, p, hp, ?_⟩
    · exact Set.mem_mul.mpr ⟨k, hk, a, ha, rfl⟩
    · have hkvX : (k : X) * (v : X) = x := congrArg Subtype.val hkv
      calc
        (k : X) * a * p = (k : X) * (a * p) := by rw [mul_assoc]
        _ = (k : X) * (v : X) := by rw [hap]
        _ = x := hkvX
  · rintro ⟨ka, hka, p, hp, hkap⟩
    rcases Set.mem_mul.mp hka with ⟨k, hk, a, ha, hkaEq⟩
    rw [← hkap, ← hkaEq]
    exact D.mul_mem (D.mul_mem (hKD hk) (hAD ha)) (hPD hp)

/-- The cyclic alternative in Lemma 9.4 is impossible when `P` is a
prime-order direct factor of `N_D(P)` but is not Sylow in `D`. -/
public theorem false_of_lemma94AlternativeB_of_internalDirectProduct
    {G : Type*} [Group G] [Finite G]
    {D P C N : Subgroup G} {t : G}
    {p : ℕ} [Fact p.Prime]
    (hPD : P ≤ D)
    (hPp : IsPGroup p P)
    (hPcard : Nat.card P = p)
    (hN : N = normalizerIn D P)
    (hprod : Section2.IsInternalDirectProduct N C P)
    (hnot : ¬ theorem4bIsSylowSubgroupOf p P D)
    (hB : Lemma94AlternativeB D D t p) :
    False := by
  classical
  rcases hB with ⟨S, hScyclic, _hSV, _hfixed⟩
  let PD : Subgroup D := P.subgroupOf D
  have hPDp : IsPGroup p PD :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨Q, hPDQ⟩ := hPDp.exists_le_sylow
  have hQcyclic : IsCyclic (Q : Subgroup D) :=
    (Sylow.equiv Q S).isCyclic.mpr hScyclic
  let R : Subgroup G := (Q : Subgroup D).map D.subtype
  have hRcyclic : IsCyclic R := by
    let e : (Q : Subgroup D) ≃* R :=
      Subgroup.equivMapOfInjective (Q : Subgroup D) D.subtype
        D.subtype_injective
    exact e.isCyclic.mp hQcyclic
  have hPR : P ≤ R := by
    intro x hxP
    let xD : D := ⟨x, hPD hxP⟩
    apply Subgroup.mem_map.mpr
    refine ⟨xD, ?_, rfl⟩
    exact hPDQ hxP
  have hRN : R ≤ N := by
    intro x hxR
    rcases Subgroup.mem_map.mp hxR with ⟨xD, hxQ, rfl⟩
    rw [hN]
    refine ⟨xD.property, centralizer_le_normalizer P ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    have hyR : y ∈ R := hPR hyP
    rcases Subgroup.mem_map.mp hyR with ⟨yD, hyQ, rfl⟩
    have hcomm := hQcyclic.isMulCommutative.is_comm.comm
      (⟨xD, hxQ⟩ : (Q : Subgroup D))
      (⟨yD, hyQ⟩ : (Q : Subgroup D))
    exact (congrArg (fun z : (Q : Subgroup D) => (z : G)) hcomm).symm
  have hRp : IsPGroup p R := Q.isPGroup'.map D.subtype
  have hRP : R = P :=
    eq_right_of_cyclic_isPGroup_of_internalDirectProduct
      hprod hRN hPR hRp hRcyclic hPcard
  exact hnot ⟨Q, hRP.symm⟩

/-- Specialization of cyclic-alternative elimination to the choices made in
Lemma 10.1. -/
public theorem false_of_choiceData_lemma94AlternativeB
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (hNormEq : normalizerIn D d.P =
      normalizerIn (peterfalviV D t) d.P)
    (hnot : ¬ theorem4bIsSylowSubgroupOf d.p d.P D)
    (hB : Lemma94AlternativeB D D t d.p) :
    False := by
  letI : Fact d.p.Prime := ⟨d.p_prime⟩
  have hPp : IsPGroup d.p d.P := by
    rw [d.P_eq_map]
    exact d.S.isPGroup'.map E.subtype
  have hPD : d.P ≤ D := d.P_le_V.trans inf_le_left
  have hA_V : d.initial.A1 ≤ peterfalviV D t := by
    rw [d.initial.A1_eq]
    exact inf_le_left
  have hprod : Section2.IsInternalDirectProduct
      (normalizerIn D d.P)
      (d.initial.A1 ⊓ Subgroup.centralizer (d.P : Set X)) d.P := by
    simpa [hNormEq] using
      (normalizer_internalDirectProduct_of_mul_eq
        (V := peterfalviV D t) (A := d.initial.A1) (P := d.P)
        (N := normalizerIn D d.P)
        hA_V d.P_le_V d.initial.A1_normal_V d.initial.V_eq_mul
        d.initial.A1_disjoint_P hNormEq)
  exact false_of_lemma94AlternativeB_of_internalDirectProduct
    hPD hPp d.card_P_eq rfl hprod hnot hB

/-- Source `(10B)`: the chosen prime-order subgroup is Sylow in the full
two-point stabilizer `D`.  Lemma 9.4 is applied with normal supplement `M`;
its fusion alternative contradicts minimality and focal transfer, while its
cyclic alternative contradicts the checked direct-factor normalizer. -/
public theorem lemma101_sylow_D
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (d : Lemma101ChoiceData
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (h43a : II1Lemma43aCoprime (X := X))
    (h43b : II1Lemma43bCyclic (X := X)) :
    theorem4bIsSylowSubgroupOf d.p d.P
      (M ⊓ rightConjugate M t) := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let V : Subgroup X := peterfalviV D t
  letI : Fact d.p.Prime := ⟨d.p_prime⟩
  have hDle : D ≤ M := inf_le_left
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hDinv : rightConjugate D t = D := by
    simpa [D] using inf_rightConjugate_invariant_of_isInvolution M ht
  have htNormD : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have hPp : IsPGroup d.p d.P := by
    rw [d.P_eq_map]
    exact d.S.isPGroup'.map (W ⊓ (M ⊓ rightConjugate M t)).subtype
  have hPne : d.P ≠ ⊥ := by
    intro hPbot
    exact d.initial.card_P_prime.ne_one (by simp [hPbot])
  have hPW : d.P ≤ W := by
    rw [d.P_eq_map]
    have hSE :
        (d.S : Subgroup ↥(W ⊓ (M ⊓ rightConjugate M t))).map
            (W ⊓ (M ⊓ rightConjugate M t)).subtype ≤
          W ⊓ (M ⊓ rightConjugate M t) :=
      Subgroup.map_subtype_le _
    exact hSE.trans inf_le_left
  have hPD : d.P ≤ D := by
    simpa [D, V] using d.P_le_V.trans inf_le_left
  have hcop : Nat.Coprime d.p
      (Nat.card (Subgroup.closure (peterfalviKSet D t))) := by
    exact h43a D t hDodd ht hDinv (by simpa [D] using hIne)
      d.p d.p_prime d.P hPp hPne (by simpa [V] using d.P_le_V)
        (PeterfalviCentralizersTrivial.subgroup hPne
          (by simpa [D] using d.P_fixedPointFree))
  have hPinfD : d.P ⊓ (derivedSubgroup D).map D.subtype = ⊥ := by
    simpa [D, E, V] using
      d.inf_derived_D_eq_bot ht hDodd htNormD hcop
  have hNormEq : normalizerIn D d.P = normalizerIn V d.P := by
    exact lemma101_normalizer_eq_of_fixedPointFree ht hDodd hDinv
      (by simpa [V] using d.P_le_V) hPne
        (by simpa [D] using d.P_fixedPointFree)
  by_contra hnot
  have hMsupp : IsNormalSupplement M D M := by
    refine ⟨le_rfl, ?_, sup_eq_left.mpr hDle⟩
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hpD : d.p ∣ Nat.card D := by
    rw [← d.card_P_eq]
    exact Subgroup.card_dvd_of_le hPD
  have hpMD : d.p ∣ Nat.card (M ⊓ D : Subgroup X) := by
    rw [inf_eq_right.mpr hDle]
    exact hpD
  have hMD : M ⊓ D = D := inf_eq_right.mpr hDle
  rcases lemma_9_4 hM ht htM d83 h84 hMsupp hpMD hIne h43b with
    hA | hB
  · rcases hA with ⟨Q, hQD, hfusion⟩
    have hQD' : (Q : Subgroup M) ≤ D.subgroupOf M := by
      rw [hMD] at hQD
      exact hQD
    have hfusion' : ControlsFusionIn (D.subgroupOf M) (Q : Subgroup M) := by
      rw [hMD] at hfusion
      exact hfusion
    exact false_of_lemma94AlternativeA hW hDle hPW hPD hPp hPne
      hPinfD Q hQD' hfusion'
  · have hB' : Lemma94AlternativeB D D t d.p := by
      rw [hMD] at hB
      exact hB
    exact false_of_choiceData_lemma94AlternativeB d hNormEq
      (by simpa [D] using hnot) hB'

/-- The `A₁`-part of `E ∩ V` lies in the derived subgroup.  An element
outside the derived subgroup would be fixed-point-free on `I`, while every
element of `A₁` centralizes the nontrivial subgroup `J=C_I(Y)`. -/
public theorem Lemma101ChoiceData.inf_A1_le_derived
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (h96 : Corollary96Conclusion D E t) :
    E ⊓ d.initial.A1 ≤ (derivedSubgroup E).map E.subtype := by
  intro x hx
  by_contra hxDer
  obtain ⟨j, hjI, hjCY, hjne⟩ := d.Y_nontrivial_centralizer
  have hjJ : j ∈ d.initial.J := by
    change j ∈ (d.initial.J : Set X)
    rw [d.initial.J_eq_centralizer]
    exact ⟨hjI, hjCY⟩
  have hxV : x ∈ peterfalviV D t := by
    have hxA := hx.2
    rw [d.initial.A1_eq] at hxA
    exact hxA.1
  have hxEV : x ∈ E ⊓ peterfalviV D t := ⟨hx.1, hxV⟩
  have hxCJ : x ∈ Subgroup.centralizer (d.initial.J : Set X) := by
    have hxA := hx.2
    rw [d.initial.A1_eq] at hxA
    exact hxA.2
  have hjx : j * x = x * j :=
    Subgroup.mem_centralizer_iff.mp hxCJ j hjJ
  exact hjne (h96.fixedPointFree x hxEV hxDer j hjI hjx)

/-- Corollary 9.6's decomposition, followed by `V=A₁P`, gives the join
factorization `E = E' ⊔ P`. -/
public theorem Lemma101ChoiceData.E_eq_derived_sup_P
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (h96 : Corollary96Conclusion D E t) :
    E = (derivedSubgroup E).map E.subtype ⊔ d.P := by
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.initial.A1
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  have hKE : K ≤ H := by
    simpa [K, H] using h96.closure_le_derived
  have hPE : d.P ≤ E := by
    rw [d.P_eq_map]
    exact Subgroup.map_subtype_le (d.S : Subgroup E)
  have hHE : H ≤ E := Subgroup.map_subtype_le (derivedSubgroup E)
  have hEA : E ⊓ A ≤ H := by
    simpa [A, H] using d.inf_A1_le_derived h96
  apply le_antisymm
  · intro x hxE
    have hxKV : x ∈ (K : Set X) * ((E ⊓ V : Subgroup X) : Set X) := by
      rw [← h96.eq_mul_fixed]
      exact hxE
    rcases Set.mem_mul.mp hxKV with ⟨k, hk, v, hv, hkv⟩
    have hvAP : v ∈ (A : Set X) * (d.P : Set X) := by
      rw [← d.initial.V_eq_mul]
      exact hv.2
    rcases Set.mem_mul.mp hvAP with ⟨a, ha, p, hp, hap⟩
    have haE : a ∈ E := by
      have haEq : a = v * p⁻¹ := by
        calc
          a = (a * p) * p⁻¹ := by simp [mul_assoc]
          _ = v * p⁻¹ := by rw [hap]
      rw [haEq]
      exact E.mul_mem hv.1 (E.inv_mem (hPE hp))
    have hkH : k ∈ H := hKE hk
    have haH : a ∈ H := hEA ⟨haE, ha⟩
    rw [← hkv, ← hap]
    exact (H ⊔ d.P).mul_mem
      ((show H ≤ H ⊔ d.P from le_sup_left) hkH)
      ((H ⊔ d.P).mul_mem
        ((show H ≤ H ⊔ d.P from le_sup_left) haH)
        ((show d.P ≤ H ⊔ d.P from le_sup_right) hp))
  · exact sup_le hHE hPE

/-- The join form of part 10.1(d) has the source set-product form. -/
public theorem Lemma101ChoiceData.E_eq_derived_mul_P
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (h96 : Corollary96Conclusion D E t) :
    (E : Set X) =
      ((derivedSubgroup E).map E.subtype : Set X) * (d.P : Set X) := by
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  have hHE : H ≤ E := Subgroup.map_subtype_le (derivedSubgroup E)
  have hPE : d.P ≤ E := by
    rw [d.P_eq_map]
    exact Subgroup.map_subtype_le (d.S : Subgroup E)
  have hHnormalE : (H.subgroupOf E).Normal := by
    have hHsub : H.subgroupOf E = derivedSubgroup E := by
      exact subgroupOf_map_subtype_eq (derivedSubgroup E)
    rw [hHsub]
    infer_instance
  have hPnormH : d.P ≤ Subgroup.normalizer (H : Set X) :=
    hPE.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hHE).mp hHnormalE)
  have hjoin : E = H ⊔ d.P := by
    simpa [H] using d.E_eq_derived_sup_P h96
  calc
    (E : Set X) = ((H ⊔ d.P : Subgroup X) : Set X) :=
      congrArg (fun Q : Subgroup X => (Q : Set X)) hjoin
    _ = (H : Set X) * (d.P : Set X) :=
      Subgroup.coe_mul_of_right_le_normalizer_left H d.P hPnormH

/-- The quotient `E/[E,E]` has the chosen prime order. -/
public theorem Lemma101ChoiceData.card_abelianization_eq_p
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (h96 : Corollary96Conclusion D E t) :
    Nat.card (E ⧸ derivedSubgroup E) = d.p := by
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let q : E →* E ⧸ derivedSubgroup E :=
    QuotientGroup.mk' (derivedSubgroup E)
  have hPE : d.P ≤ E := by
    rw [d.P_eq_map]
    exact Subgroup.map_subtype_le (d.S : Subgroup E)
  let i : d.P →* E := Subgroup.inclusion hPE
  let f : d.P →* E ⧸ derivedSubgroup E := q.comp i
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (derivedSubgroup E) z
    have heProd : (e : X) ∈ (H : Set X) * (d.P : Set X) := by
      rw [← d.E_eq_derived_mul_P h96]
      exact e.property
    rcases Set.mem_mul.mp heProd with ⟨h, hh, p, hp, hhp⟩
    rcases Subgroup.mem_map.mp hh with ⟨hE, hhE, hhval⟩
    let pE : E := ⟨p, hPE hp⟩
    have heq : hE * pE = e := by
      apply Subtype.ext
      change (hE : X) * p = (e : X)
      change (hE : X) = h at hhval
      rw [hhval, hhp]
    refine ⟨(⟨p, hp⟩ : d.P), ?_⟩
    change q pE = q e
    rw [← heq]
    have hqh : q hE = 1 := by
      exact (QuotientGroup.eq_one_iff (N := derivedSubgroup E) (x := hE)).2 hhE
    calc
      q pE = 1 * q pE := (one_mul _).symm
      _ = q hE * q pE := by rw [hqh]
      _ = q (hE * pE) := (map_mul q hE pE).symm
  have hle : Nat.card (E ⧸ derivedSubgroup E) ≤ Nat.card d.P :=
    Nat.card_le_card_of_surjective f hsurj
  rw [d.card_P_eq] at hle
  have hge : d.p ≤ Nat.card (E ⧸ derivedSubgroup E) :=
    Nat.le_of_dvd Nat.card_pos d.p_dvd_abelianization
  exact Nat.le_antisymm hle hge

private theorem lemma101_coprime_card_sup_of_left_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    {K A : Subgroup G}
    (hKnormal : K.Normal)
    (hKcop : Nat.Coprime p (Nat.card K))
    (hAcop : Nat.Coprime p (Nat.card A)) :
    Nat.Coprime p (Nat.card (K ⊔ A : Subgroup G)) := by
  letI : K.Normal := hKnormal
  have hmul : ((K ⊔ A : Subgroup G) : Set G) =
      (A : Set G) * (K : Set G) := by
    simpa [sup_comm] using Subgroup.mul_normal A K
  have hcardSup : Nat.card (K ⊔ A : Subgroup G) =
      Nat.card ((A : Set G) * (K : Set G) : Set G) :=
    Nat.card_congr (Set.equivOfEq hmul)
  have hcardMul : Nat.card ((A : Set G) * (K : Set G) : Set G) =
      Nat.card K * Nat.card (((A : Set G).image (↑) : Set (G ⧸ K))) := by
    simpa using
      (Subgroup.card_mul_eq_card_subgroup_mul_card_quotient
        (s := K) (t := (A : Set G)))
  have hsetImage :
      ((A : Set G).image (↑) : Set (G ⧸ K)) =
        (A.map (QuotientGroup.mk' K) : Set (G ⧸ K)) := by
    simp [Subgroup.coe_map]
  have hcardImage :
      Nat.card (((A : Set G).image (↑) : Set (G ⧸ K))) =
        Nat.card (A.map (QuotientGroup.mk' K)) :=
    Nat.card_congr (Set.equivOfEq hsetImage)
  have himageDvd : Nat.card (A.map (QuotientGroup.mk' K)) ∣ Nat.card A :=
    Subgroup.card_map_dvd A (QuotientGroup.mk' K)
  have himageCop : Nat.Coprime p
      (Nat.card (((A : Set G).image (↑) : Set (G ⧸ K)))) := by
    rw [hcardImage]
    exact Nat.Coprime.of_dvd_right himageDvd hAcop
  rw [hcardSup, hcardMul]
  exact hKcop.mul_right himageCop

/-- The normal `p'`-subgroup generated by the Peterfalvi kernel and `A₁`
is the ambient `p'`-core of `D`. -/
public theorem Lemma101ChoiceData.kernel_sup_A1_eq_pPrimeCore
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (d : Lemma101ChoiceData D E (peterfalviV D t) t)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hcop : Nat.Coprime d.p
      (Nat.card (Subgroup.closure (peterfalviKSet D t))))
    (hPsylD : theorem4bIsSylowSubgroupOf d.p d.P D) :
    Subgroup.closure (peterfalviKSet D t) ⊔ d.initial.A1 =
      (pPrimeCore d.p D).map D.subtype := by
  classical
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.initial.A1
  let P : Subgroup X := d.P
  let N : Subgroup X := K ⊔ A
  let O : Subgroup X := (pPrimeCore d.p D).map D.subtype
  letI : Fact d.p.Prime := ⟨d.p_prime⟩
  have hKD : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hVD : V ≤ D := inf_le_left
  have hAV : A ≤ V := by
    dsimp [A, V]
    rw [d.initial.A1_eq]
    exact inf_le_left
  have hPV : P ≤ V := d.P_le_V
  have hAD : A ≤ D := hAV.trans hVD
  have hPD : P ≤ D := hPV.trans hVD
  have hVsup : A ⊔ P = V := by
    apply le_antisymm
    · exact sup_le hAV hPV
    · intro x hxV
      have hxprod : x ∈ (A : Set X) * (P : Set X) := by
        rw [← d.initial.V_eq_mul]
        exact hxV
      rcases Set.mem_mul.mp hxprod with ⟨a, ha, p, hp, hap⟩
      rw [← hap]
      exact Subgroup.mul_mem_sup ha hp
  have hDsup : K ⊔ V = D := by
    simpa [K, V] using lemma101_peterfalviKernel_sup_fixed_eq ht hDodd hDnorm
  have hKnormal : (K.subgroupOf D).Normal := by
    simpa [K] using lemma101_peterfalviKernel_normal ht hDodd hDnorm
  have hND : N ≤ D := sup_le hKD hAD
  have hKnormN : K ≤ Subgroup.normalizer (N : Set X) :=
    (show K ≤ N from le_sup_left).trans Subgroup.le_normalizer
  have hVnormK : V ≤ Subgroup.normalizer (K : Set X) :=
    hVD.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKD).mp hKnormal)
  have hVnormA : V ≤ Subgroup.normalizer (A : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAV).mp
      d.initial.A1_normal_V
  have hVnormN : V ≤ Subgroup.normalizer (N : Set X) := by
    simpa [N] using lemma101_le_normalizer_sup_of_normalizes hVnormK hVnormA
  have hDnormN : D ≤ Subgroup.normalizer (N : Set X) := by
    rw [← hDsup]
    exact sup_le hKnormN hVnormN
  have hNnormal : (N.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hND).mpr hDnormN
  have hAeq : A = (pPrimeCore d.p V).map V.subtype := by
    simpa [A, V] using d.A1_eq_pPrimeCore hPsylD
  have hAcop : Nat.Coprime d.p (Nat.card A) := by
    rw [hAeq, Subgroup.card_map_of_injective V.subtype_injective]
    exact pPrimeCore_coprime_card
  have hNcop : Nat.Coprime d.p (Nat.card N) := by
    let KD : Subgroup D := K.subgroupOf D
    let AD : Subgroup D := A.subgroupOf D
    let ND : Subgroup D := N.subgroupOf D
    have hND_eq : ND = KD ⊔ AD := by
      simpa [ND, KD, AD, N] using Subgroup.subgroupOf_sup hKD hAD
    have hKDcop : Nat.Coprime d.p (Nat.card KD) := by
      rw [show Nat.card KD = Nat.card K by exact natCard_subgroupOf_eq K D hKD]
      exact hcop
    have hADcop : Nat.Coprime d.p (Nat.card AD) := by
      rw [show Nat.card AD = Nat.card A by exact natCard_subgroupOf_eq A D hAD]
      exact hAcop
    have hNDcop : Nat.Coprime d.p (Nat.card ND) := by
      rw [hND_eq]
      exact lemma101_coprime_card_sup_of_left_normal hKnormal hKDcop hADcop
    have hNDcard : Nat.card ND = Nat.card N := natCard_subgroupOf_eq N D hND
    rwa [hNDcard] at hNDcop
  letI : (N.subgroupOf D).Normal := hNnormal
  have hNO : N ≤ O := by
    simpa [O] using subgroupOf_le_pPrimeCore_map hND hNcop
  have hNsupP : N ⊔ P = D := by
    calc
      N ⊔ P = K ⊔ (A ⊔ P) := by simp [N, sup_assoc]
      _ = K ⊔ V := by rw [hVsup]
      _ = D := hDsup
  have hOcop : Nat.Coprime d.p (Nat.card O) := by
    have hcardO : Nat.card O = Nat.card (pPrimeCore d.p D) :=
      Subgroup.card_map_of_injective D.subtype_injective
    rw [hcardO]
    exact pPrimeCore_coprime_card
  have hPOdisj : Disjoint P O := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [d.card_P_eq]
    exact hOcop
  have hPnormN : P ≤ Subgroup.normalizer (N : Set X) := hPD.trans hDnormN
  apply le_antisymm
  · exact hNO
  · intro x hxO
    have hxD : x ∈ D := (Subgroup.map_subtype_le (pPrimeCore d.p D)) hxO
    have hxNP : x ∈ (N : Set X) * (P : Set X) := by
      have hxJoin : x ∈ N ⊔ P := by
        rw [hNsupP]
        exact hxD
      change x ∈ ((N ⊔ P : Subgroup X) : Set X) at hxJoin
      rw [Subgroup.coe_mul_of_right_le_normalizer_left N P hPnormN] at hxJoin
      exact hxJoin
    rcases Set.mem_mul.mp hxNP with ⟨n, hn, p, hp, hnp⟩
    have hnO : n ∈ O := hNO hn
    have hpO : p ∈ O := by
      have hpEq : p = n⁻¹ * x := by
        calc
          p = n⁻¹ * (n * p) := by simp
          _ = n⁻¹ * x := by rw [hnp]
      rw [hpEq]
      exact O.mul_mem (O.inv_mem hnO) hxO
    have hpOne : p = 1 := Subgroup.disjoint_def.mp hPOdisj hp hpO
    have hxEq : x = n := by
      calc
        x = n * p := hnp.symm
        _ = n := by rw [hpOne]; simp
    rwa [hxEq]

private theorem lemma101_normalizer_ne_centralizer_of_sylow_M
    {X : Type u} [Group X] [Finite X]
    {M D W P : Subgroup X} {p : ℕ}
    (hp : Nat.Prime p)
    (hW : IsMinimalNormalSupplement M D W)
    (hPW : P ≤ W)
    (hPD : P ≤ D)
    (hPp : IsPGroup p P)
    (hPne : P ≠ ⊥)
    (hPsylM : theorem4bIsSylowSubgroupOf p P M) :
    normalizerIn M P ≠ M ⊓ Subgroup.centralizer (P : Set X) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsylM with ⟨Q, hPmap⟩
  have hQD : (Q : Subgroup M) ≤ D.subgroupOf M := by
    intro x hxQ
    change (x : X) ∈ D
    apply hPD
    rw [hPmap]
    exact Subgroup.mem_map_of_mem M.subtype hxQ
  have hres : External.hallPResidual p W = ⊤ :=
    hallPResidual_eq_top_of_minimalNormalSupplement hW Q hQD
  let PW : Subgroup W := P.subgroupOf W
  have hPWp : IsPGroup p PW :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPW).symm
  have hPWcomm : PW ≤ commutator W :=
    isPGroup_le_commutator_of_hallPResidual_eq_top hPWp hres
  have hPcommM : P ≤ (commutator M).map M.subtype := by
    intro x hxP
    have hxW : (⟨x, hPW hxP⟩ : W) ∈ PW := hxP
    have hxcommW : (⟨x, hPW hxP⟩ : W) ∈ commutator W := hPWcomm hxW
    have hxmapW : x ∈ (commutator W).map W.subtype :=
      Subgroup.mem_map_of_mem W.subtype hxcommW
    rw [Subgroup.map_subtype_commutator] at hxmapW
    have hxcommM : x ∈ ⁅M, M⁆ :=
      Subgroup.commutator_mono hW.prop.le_M hW.prop.le_M hxmapW
    rw [Subgroup.map_subtype_commutator]
    exact hxcommM
  intro hEq
  have hNormCent :
      Subgroup.normalizer ((Q : Subgroup M) : Set M) ≤
        Subgroup.centralizer ((Q : Subgroup M) : Set M) := by
    intro n hn
    have hnMapNorm : (n : X) ∈ Subgroup.normalizer (P : Set X) := by
      rw [hPmap]
      apply Subgroup.le_normalizer_map (H := (Q : Subgroup M)) M.subtype
      exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    have hnLocal : (n : X) ∈ normalizerIn M P := ⟨n.property, hnMapNorm⟩
    have hnCent : (n : X) ∈ Subgroup.centralizer (P : Set X) := by
      rw [hEq] at hnLocal
      exact hnLocal.2
    rw [Subgroup.mem_centralizer_iff]
    intro q hqQ
    have hqP : (q : X) ∈ P := by
      rw [hPmap]
      exact Subgroup.mem_map_of_mem M.subtype hqQ
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp hnCent (q : X) hqP)
  letI : IsMulCommutative (Q : Subgroup M) :=
    ⟨⟨fun a b => Subtype.ext
      (hNormCent (Subgroup.le_normalizer b.2) a a.2)⟩⟩
  let tr := MonoidHom.transferSylow Q hNormCent
  have hQker : (Q : Subgroup M) ≤ tr.ker := by
    intro q hqQ
    apply Abelianization.commutator_subset_ker tr
    have hqP : (q : X) ∈ P := by
      rw [hPmap]
      exact Subgroup.mem_map_of_mem M.subtype hqQ
    have hqMapComm : (q : X) ∈ (commutator M).map M.subtype := hPcommM hqP
    rcases Subgroup.mem_map.mp hqMapComm with ⟨y, hyComm, hyq⟩
    have hyEq : y = q := Subtype.ext hyq
    simpa [hyEq] using hyComm
  have hcomp : tr.ker.IsComplement' (Q : Subgroup M) :=
    MonoidHom.ker_transferSylow_isComplement' Q hNormCent
  have hQbot : (Q : Subgroup M) = ⊥ := by
    rw [eq_bot_iff]
    intro q hqQ
    have hqInf : q ∈ tr.ker ⊓ (Q : Subgroup M) := ⟨hQker hqQ, hqQ⟩
    have hinf : tr.ker ⊓ (Q : Subgroup M) = ⊥ :=
      disjoint_iff.mp hcomp.disjoint
    simpa [hinf] using hqInf
  apply hPne
  rw [hPmap, hQbot, Subgroup.map_bot]

/-- Source Lemma 10.1(e), in ambient-subgroup form.  Burnside transfer is
applied directly, so no additional `[IG; 16.5]` callback is required. -/
public theorem lemma101_centralizer_lt_normalizer_of_sylow_M
    {X : Type u} [Group X] [Finite X]
    {M D W P : Subgroup X} {p : ℕ}
    (hp : Nat.Prime p)
    (hW : IsMinimalNormalSupplement M D W)
    (hPW : P ≤ W)
    (hPD : P ≤ D)
    (hPp : IsPGroup p P)
    (hPne : P ≠ ⊥)
    (hPsylM : theorem4bIsSylowSubgroupOf p P M) :
    M ⊓ Subgroup.centralizer (P : Set X) < normalizerIn M P := by
  apply lt_of_le_of_ne
  · exact inf_le_inf_left M (centralizer_le_normalizer P)
  · exact (lemma101_normalizer_ne_centralizer_of_sylow_M
      hp hW hPW hPD hPp hPne hPsylM).symm

/-- Lemma 10.1(e) specialized to its chosen prime-order subgroup. -/
public theorem Lemma101ChoiceData.centralizer_lt_normalizer_of_sylow_M
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101ChoiceData
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hPsylM : theorem4bIsSylowSubgroupOf d.p d.P M) :
    M ⊓ Subgroup.centralizer (d.P : Set X) < normalizerIn M d.P := by
  have hPW : d.P ≤ W := by
    rw [d.P_eq_map]
    have hSE :
        (d.S : Subgroup ↥( W ⊓ (M ⊓ rightConjugate M t))).map
            (W ⊓ (M ⊓ rightConjugate M t)).subtype ≤
          W ⊓ (M ⊓ rightConjugate M t) :=
      Subgroup.map_subtype_le _
    exact hSE.trans inf_le_left
  have hPD : d.P ≤ M ⊓ rightConjugate M t :=
    d.P_le_V.trans inf_le_left
  have hPp : IsPGroup d.p d.P := by
    rw [d.P_eq_map]
    exact d.S.isPGroup'.map
      (W ⊓ (M ⊓ rightConjugate M t)).subtype
  have hPne : d.P ≠ ⊥ := by
    intro hPbot
    exact d.initial.card_P_prime.ne_one (by simp [hPbot])
  exact lemma101_centralizer_lt_normalizer_of_sylow_M
    d.p_prime hW hPW hPD hPp hPne hPsylM

/-- The source data and conclusions of Lemma 10.1.  This is Type-valued so
Sections 10--11 can reuse the chosen prime and subgroups. -/
public structure Lemma101Conclusion
    {X : Type u} [Group X] [Finite X]
    (M W D E V : Subgroup X) (t : X) where
  choice : Lemma101ChoiceData D E V t
  P_card : Nat.card choice.P = choice.p
  P_sylow_E_inf_V : theorem4bIsSylowSubgroupOf choice.p choice.P (E ⊓ V)
  A1_eq_pPrimeCore :
    choice.initial.A1 = (pPrimeCore choice.p V).map V.subtype
  V_eq_mul :
    (V : Set X) = (choice.initial.A1 : Set X) * (choice.P : Set X)
  centralizer_A1 :
    (choice.initial.J : Set X) =
      {x : X | x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (choice.initial.A1 : Set X)}
  centralizer_A1_card : Nat.card choice.initial.J = 2 ^ choice.p - 1
  centralizer_uniform :
    ∀ (B : Subgroup X), B ≤ choice.initial.A1 → B ≠ ⊥ →
      choice.P ≤ Subgroup.normalizer (B : Set X) →
      {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (B : Set X)} =
        {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (choice.initial.A1 : Set X)}
  normalizer_factorization :
    normalizerIn D choice.P =
        (choice.initial.A1 ⊓ Subgroup.centralizer (choice.P : Set X)) ⊔ choice.P ∧
      (normalizerIn D choice.P : Set X) =
        ((choice.initial.A1 ⊓ Subgroup.centralizer (choice.P : Set X)) : Set X) *
          (choice.P : Set X) ∧
      Disjoint (choice.initial.A1 ⊓ Subgroup.centralizer (choice.P : Set X)) choice.P
  D_eq_kernel_mul_A1_mul_P :
    (D : Set X) =
      (Subgroup.closure (peterfalviKSet D t) : Set X) *
        (choice.initial.A1 : Set X) * (choice.P : Set X)
  P_sylow_D : theorem4bIsSylowSubgroupOf choice.p choice.P D
  kernel_sup_A1_eq_pPrimeCore :
    Subgroup.closure (peterfalviKSet D t) ⊔ choice.initial.A1 =
      (pPrimeCore choice.p D).map D.subtype
  E_eq_derived_mul_P :
    (E : Set X) =
      ((derivedSubgroup E).map E.subtype : Set X) * (choice.P : Set X)
  card_abelianization_eq_p : Nat.card (E ⧸ derivedSubgroup E) = choice.p
  normalizer_growth_if_sylow_M :
    theorem4bIsSylowSubgroupOf choice.p choice.P M →
      M ⊓ Subgroup.centralizer (choice.P : Set X) < normalizerIn M choice.P

/-- Source Lemma 10.1, assembled from Corollary 9.6, Proposition 9.3,
Corollary 8.5, the checked source (10B), and Burnside transfer. -/
public theorem lemma_10_1
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (h96 : Corollary96Conclusion
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t)
    (h93 : Proposition93Conclusion
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t)
    (h43a : II1Lemma43aCoprime (X := X))
    (h43b : II1Lemma43bCyclic (X := X)) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    let E : Subgroup X := W ⊓ D
    let V : Subgroup X := peterfalviV D t
    Nonempty (Lemma101Conclusion M W D E V t) := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let V : Subgroup X := peterfalviV D t
  have hEodd : Odd (Nat.card E) := by
    apply (hM.inf_rightConjugate_card_odd htM).of_dvd_nat
    simpa [D, E] using (Subgroup.card_dvd_of_le (inf_le_right : E ≤ D))
  have hEne : E ≠ ⊥ := by
    intro hEbot
    apply h96.inf_fixed_ne_bot
    simpa [D, E, V, hEbot]
  have h95 : ∀ p : ℕ, Nat.Prime p →
      p ∣ Nat.card (E ⧸ derivedSubgroup E) →
      Lemma94AlternativeB D E t p := by
    intro p hp hpAb
    letI : Fact p.Prime := ⟨hp⟩
    simpa [D, E] using
      corollary_9_5_ambient_abelianization hM ht htM d83 h84 hW hpAb
        hIne h43b
  have hexists : Nonempty (Lemma101ChoiceData D E V t) := by
    simpa [D, E, V] using
      lemma101_exists_choice_data hM ht htM d83 h84 hEodd hEne h95 h93
  obtain ⟨d⟩ := hexists
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hDinv : rightConjugate D t = D := by
    simpa [D] using inf_rightConjugate_invariant_of_isInvolution M ht
  have hDnorm : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have hPp : IsPGroup d.p d.P := by
    rw [d.P_eq_map]
    exact d.S.isPGroup'.map E.subtype
  have hPne : d.P ≠ ⊥ := by
    intro hPbot
    exact d.initial.card_P_prime.ne_one (by simp [hPbot])
  have hcop : Nat.Coprime d.p
      (Nat.card (Subgroup.closure (peterfalviKSet D t))) := by
    exact h43a D t hDodd ht hDinv (by simpa [D] using hIne)
      d.p d.p_prime d.P hPp hPne (by simpa [V] using d.P_le_V)
        (PeterfalviCentralizersTrivial.subgroup hPne
          (by simpa [D] using d.P_fixedPointFree))
  have hPsylD : theorem4bIsSylowSubgroupOf d.p d.P D := by
    simpa [D, E, V] using
      lemma101_sylow_D hM ht htM d83 h84 hW d
        (by simpa [D] using hIne) h43a h43b
  have hNormEq : normalizerIn D d.P = normalizerIn V d.P := by
    exact lemma101_normalizer_eq_of_fixedPointFree ht hDodd hDinv
      (by simpa [V] using d.P_le_V) hPne
        (by simpa [D] using d.P_fixedPointFree)
  have hUniform := d.centralizer_uniform hM ht htM d83 h84
  have hPE : d.P ≤ E := by
    rw [d.P_eq_map]
    exact Subgroup.map_subtype_le (d.S : Subgroup E)
  have hPsylEV : theorem4bIsSylowSubgroupOf d.p d.P (E ⊓ V) :=
    theorem4bIsSylowSubgroupOf_of_between d.p_prime d.P_isSylow_E
      (le_inf hPE d.P_le_V) inf_le_left
  have hUniformSets : ∀ (B : Subgroup X), B ≤ d.initial.A1 → B ≠ ⊥ →
      d.P ≤ Subgroup.normalizer (B : Set X) →
      {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (B : Set X)} =
        {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (d.initial.A1 : Set X)} := by
    intro B hBA hBne hPnormB
    obtain ⟨J, hJset, hJeq⟩ := hUniform.2 B hBA hBne hPnormB
    calc
      {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (B : Set X)} = (J : Set X) := hJset.symm
      _ = (d.initial.J : Set X) :=
        congrArg (fun H : Subgroup X => (H : Set X)) hJeq
      _ = {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.centralizer (d.initial.A1 : Set X)} := by
        simpa [D] using hUniform.1
  refine ⟨{
    choice := d
    P_card := d.card_P_eq
    P_sylow_E_inf_V := hPsylEV
    A1_eq_pPrimeCore := d.A1_eq_pPrimeCore hPsylD
    V_eq_mul := d.initial.V_eq_mul
    centralizer_A1 := by simpa [D] using hUniform.1
    centralizer_A1_card := by simpa [d.card_P_eq] using d.initial.J_card
    centralizer_uniform := hUniformSets
    normalizer_factorization := d.normalizer_factorization hNormEq
    D_eq_kernel_mul_A1_mul_P :=
      d.D_eq_kernel_mul_A1_mul_P ht hDodd hDnorm
    P_sylow_D := hPsylD
    kernel_sup_A1_eq_pPrimeCore :=
      d.kernel_sup_A1_eq_pPrimeCore ht hDodd hDnorm hcop hPsylD
    E_eq_derived_mul_P := d.E_eq_derived_mul_P h96
    card_abelianization_eq_p := d.card_abelianization_eq_p h96
    normalizer_growth_if_sylow_M := fun hPsylM =>
      d.centralizer_lt_normalizer_of_sylow_M hW hPsylM }⟩


end CFSG.BenderSuzuki
