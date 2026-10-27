module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Emb
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413AutX
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413StrNorm
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Ord
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413CaseI

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag

open scoped commutatorElement

theorem asch1413_sp4_caseI {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {ρ : Q →* MulAut V} (hρ : Function.Injective ρ)
    {L A : Subgroup Q} (hF : genFittingFStar Q = L) (hZL : Subgroup.center ↥L = ⊥)
    {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) (h7 : 7 ≤ Nat.card K)
    (e : ↥L ≃* StatedProj (StatedSp 2 K))
    (hC : ∀ v : V, (∀ l ∈ L, ρ l v = v) → v = 1)
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) (hq : IsQuadraticOn ρ A)
    {z : Q} (hzA : z ∈ A) (hzL : z ∈ L) (hzD : IsConj (u1 K) (e ⟨z, hzL⟩)) : False := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have h5 : 5 ≤ Nat.card K := by omega
  have hLsub : CFSG.ComponentClassification.GeneralizedFitting.subgroup Q = L := hF
  haveI hLn : L.Normal := hLsub ▸ CFSG.ComponentClassification.GeneralizedFitting.normal Q
  have hcenL : centralizer (L : Set Q) ≤ L :=
    hLsub ▸ CFSG.ComponentClassification.GeneralizedFitting.centralizer_le Q
  obtain ⟨r, hr⟩ := isConj_iff.mp hzD
  let e' : ↥L ≃* StatedProj (StatedSp 2 K) := e.trans (MulAut.conj r⁻¹)
  have hz'e : e' ⟨z, hzL⟩ = u1 K := by
    show (MulAut.conj r⁻¹) (e ⟨z, hzL⟩) = u1 K
    rw [MulAut.conj_apply, ← hr]
    group
  have hZ : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥ := by
    have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e'
    rw [hZL, Subgroup.map_bot] at h
    exact h.symm
  obtain ⟨θ, hθinj, hθconj, hθapp, _hθinner, _hθrange⟩ := a1413_embedding hLn hcenL e' hZ
  let XL : Subgroup ↥L := (X0 K).comap e'.toMonoidHom
  let X : Subgroup Q := XL.map L.subtype
  have hX0eq : XL.map e'.toMonoidHom = X0 K :=
    Subgroup.map_comap_eq_self_of_surjective e'.surjective (X0 K)
  have hXL : X ≤ L := by
    rintro x ⟨l, -, rfl⟩
    exact l.2
  have hXperf : ⁅X, X⁆ = X := by
    have hperf0 : ⁅XL, XL⁆ = XL := by
      apply Subgroup.map_injective (f := e'.toMonoidHom) e'.injective
      rw [Subgroup.map_commutator, hX0eq, a1413StrPerfect_X0 h2 h4]
    change ⁅XL.map L.subtype, XL.map L.subtype⁆ = XL.map L.subtype
    rw [← Subgroup.map_commutator (H₁ := XL) (H₂ := XL) (f := L.subtype), hperf0]
  have hXz : X ≤ centralizer ({z} : Set Q) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_centralizer_singleton_iff]
    have hcomm : e' l * u1 K = u1 K * e' l :=
      mem_centralizer_singleton_iff.mp (X0_le_centralizer hl)
    have hcommL : l * ⟨z, hzL⟩ = ⟨z, hzL⟩ * l := by
      apply e'.injective
      rw [map_mul, map_mul, hz'e]
      exact hcomm
    simpa using congrArg Subtype.val hcommL
  have hz2 : orderOf z = 2 := by
    have hu1ord : orderOf (u1 K) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)
    calc orderOf z = orderOf ((⟨z, hzL⟩ : ↥L) : Q) := rfl
      _ = orderOf (⟨z, hzL⟩ : ↥L) := Subgroup.orderOf_coe _
      _ = orderOf (e' ⟨z, hzL⟩) :=
          (orderOf_injective e'.toMonoidHom e'.injective _).symm
      _ = orderOf (u1 K) := by rw [hz'e]
      _ = 2 := hu1ord
  have hCX : ∀ y : Q, (∀ x ∈ X, y * x = x * y) → y ∈ zpowers z := by
    intro y hy
    have hfix1 : ∀ x ∈ E1 K, θ y x = x := by
      intro x hx
      obtain ⟨l, rfl⟩ := e'.surjective x
      have hl : l ∈ XL := (E1_le_X0 h2) hx
      have hXl : (l : Q) ∈ X := Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
      have hcomm : y * (l : Q) = (l : Q) * y := hy (l : Q) hXl
      have hconj : y * (l : Q) * y⁻¹ = (l : Q) := by rw [hcomm]; group
      rw [hθapp y l]
      exact congrArg e' (Subtype.ext hconj)
    have hfix2 : ∀ x ∈ E2 K, θ y x = x := by
      intro x hx
      obtain ⟨l, rfl⟩ := e'.surjective x
      have hl : l ∈ XL := (E2_le_X0 h2) hx
      have hXl : (l : Q) ∈ X := Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
      have hcomm : y * (l : Q) = (l : Q) * y := hy (l : Q) hXl
      have hconj : y * (l : Q) * y⁻¹ = (l : Q) := by rw [hcomm]; group
      rw [hθapp y l]
      exact congrArg e' (Subtype.ext hconj)
    rcases psp4_aut_fix_E1E2 hodd h5 (θ y) hfix1 hfix2 with h1 | h1
    · have hy1 : y = 1 := hθinj (h1.trans (map_one θ).symm)
      rw [hy1]
      exact Subgroup.one_mem _
    · have hzθ : θ z = MulAut.conj (u1 K) := by
        simpa only [hz'e] using hθconj ⟨z, hzL⟩
      have hyz : y = z := hθinj (h1.trans hzθ.symm)
      rw [hyz]
      exact Subgroup.mem_zpowers z
  have hnorm : ∀ N : Subgroup Q, N ≤ L → N ≤ centralizer ({z} : Set Q) →
      (∀ c ∈ L, c * z = z * c → ∀ n ∈ N, c * n * c⁻¹ ∈ N) → z ∈ N →
      ¬ N ≤ zpowers z → X ≤ N := by
    intro N hNL hNC hNnorm hzN hNne
    let NL : Subgroup ↥L := N.comap L.subtype
    let NP : Subgroup (StatedProj (StatedSp 2 K)) := NL.map e'.toMonoidHom
    have hNCP : NP ≤ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))) := by
      intro n hn
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hn
      rw [mem_centralizer_singleton_iff]
      change e' l * u1 K = u1 K * e' l
      have hcommQ : (l : Q) * z = z * (l : Q) :=
        mem_centralizer_singleton_iff.mp (hNC hl)
      have hcommL : l * ⟨z, hzL⟩ = ⟨z, hzL⟩ * l := Subtype.ext hcommQ
      have hcommE : e' l * e' ⟨z, hzL⟩ = e' ⟨z, hzL⟩ * e' l := by
        rw [← map_mul, ← map_mul, hcommL]
      simpa only [hz'e] using hcommE
    have hNPnorm : ∀ c ∈ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))),
        ∀ n ∈ NP, c * n * c⁻¹ ∈ NP := by
      intro c hc n hn
      let lc : ↥L := e'.symm c
      have hclc : e' lc = c := e'.apply_symm_apply c
      obtain ⟨l, hl, hln⟩ := Subgroup.mem_map.mp hn
      have hcommC : c * u1 K = u1 K * c := mem_centralizer_singleton_iff.mp hc
      have hcommL : lc * ⟨z, hzL⟩ = ⟨z, hzL⟩ * lc := by
        apply e'.injective
        rw [map_mul, map_mul, hz'e, hclc]
        exact hcommC
      have hcommZ : (lc : Q) * z = z * (lc : Q) := congrArg Subtype.val hcommL
      have hmemN : (lc : Q) * (l : Q) * (lc : Q)⁻¹ ∈ N :=
        hNnorm (lc : Q) lc.2 hcommZ (l : Q) hl
      refine Subgroup.mem_map.mpr ⟨lc * l * lc⁻¹, ?_, ?_⟩
      · show ((lc * l * lc⁻¹ : ↥L) : Q) ∈ N
        simpa using hmemN
      · rw [← hln]
        change e' (lc * l * lc⁻¹) = c * e' l * c⁻¹
        rw [map_mul, map_mul, map_inv, hclc]
    have hu1NP : u1 K ∈ NP := by
      refine Subgroup.mem_map.mpr ⟨⟨z, hzL⟩, ?_, hz'e⟩
      exact hzN
    have hNPne : ¬ NP ≤ zpowers (u1 K) := by
      intro hle
      apply hNne
      intro n hn
      have hnL : n ∈ L := hNL hn
      let nl : ↥L := ⟨n, hnL⟩
      have hmem : e' nl ∈ zpowers (u1 K) :=
        hle (Subgroup.mem_map.mpr ⟨nl, hn, rfl⟩)
      have hzpow : zpowers (e' ⟨z, hzL⟩) =
          (Subgroup.zpowers (⟨z, hzL⟩ : ↥L)).map e'.toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        rfl
      rw [← hz'e, hzpow] at hmem
      obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp hmem
      have hnl : nl = m := (e'.injective hmeq).symm
      have hmemz : nl ∈ Subgroup.zpowers (⟨z, hzL⟩ : ↥L) := hnl ▸ hm
      have hmap : (Subgroup.zpowers (⟨z, hzL⟩ : ↥L)).map L.subtype = zpowers z := by
        rw [MonoidHom.map_zpowers]
        rfl
      have : n ∈ (Subgroup.zpowers (⟨z, hzL⟩ : ↥L)).map L.subtype :=
        Subgroup.mem_map.mpr ⟨nl, hmemz, rfl⟩
      rwa [hmap] at this
    have hX0le : X0 K ≤ NP := by
      have h := psp4_derived_le_of_normalized hodd h7 (IsConj.refl (u1 K)) NP
        hNCP hNPnorm hu1NP hNPne
      rwa [a1413StrCommutator_C_eq_X0 h2 h4] at h
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : e' l ∈ NP := hX0le hl
    obtain ⟨n, hn, hneq⟩ := Subgroup.mem_map.mp hmem
    have hnl : n = l := e'.injective hneq
    have : (n : Q) ∈ N := hn
    rw [← hnl]
    exact hn
  have hgen : ∀ h ∈ L, h * z * h⁻¹ ≠ z → (h * z * h⁻¹) * z = z * (h * z * h⁻¹) →
      L ≤ X ⊔ X.map (MulAut.conj h).toMonoidHom := by
    intro h hhL hne hcomm
    let hl : ↥L := ⟨h, hhL⟩
    have hne' : e' hl * u1 K * (e' hl)⁻¹ ≠ u1 K := by
      intro heq
      apply hne
      have h1 : e' (hl * ⟨z, hzL⟩ * hl⁻¹) = e' ⟨z, hzL⟩ := by
        rw [map_mul, map_mul, map_inv, hz'e]
        exact heq
      exact congrArg Subtype.val (e'.injective h1)
    have hcomm' : (e' hl * u1 K * (e' hl)⁻¹) * u1 K =
        u1 K * (e' hl * u1 K * (e' hl)⁻¹) := by
      have h1 : e' hl * u1 K * (e' hl)⁻¹ = e' (hl * ⟨z, hzL⟩ * hl⁻¹) := by
        rw [map_mul, map_mul, map_inv, hz'e]
      rw [h1, ← hz'e, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    let Y : Subgroup (StatedProj (StatedSp 2 K)) :=
      (X0 K).map (MulAut.conj (e' hl)).toMonoidHom
    have hsup : X0 K ⊔ Y = ⊤ := by
      have h := psp4_sup_conj_derived_eq_top hodd h7 (IsConj.refl (u1 K)) (e' hl) hne' hcomm'
      rwa [a1413StrCommutator_C_eq_X0 h2 h4] at h
    have hcomap : Y.comap e'.toMonoidHom = XL.map (MulAut.conj hl).toMonoidHom := by
      ext c
      constructor
      · intro hc
        have hc' : e' c ∈ Y := hc
        obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hc'
        obtain ⟨b, rfl⟩ := e'.surjective y
        refine Subgroup.mem_map.mpr ⟨b, hy, ?_⟩
        apply e'.injective
        change e' ((MulAut.conj hl) b) = e' c
        rw [MulAut.conj_apply, map_mul, map_mul, map_inv, ← hyc]
        rfl
      · rintro ⟨b, hb, rfl⟩
        refine Subgroup.mem_map.mpr ⟨e' b, ?_, ?_⟩
        · exact hb
        · change (MulAut.conj (e' hl)) (e' b) = e' ((MulAut.conj hl) b)
          rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    have hsupL : XL ⊔ XL.map (MulAut.conj hl).toMonoidHom = ⊤ := by
      have h : XL ⊔ Y.comap e'.toMonoidHom = ⊤ := by
        change (X0 K).comap e'.toMonoidHom ⊔ Y.comap e'.toMonoidHom = ⊤
        rw [Subgroup.comap_sup_eq e'.toMonoidHom (X0 K) Y e'.surjective, hsup,
          Subgroup.comap_top]
      rwa [hcomap] at h
    have hcomp : L.subtype.comp (MulAut.conj hl).toMonoidHom =
        (MulAut.conj h).toMonoidHom.comp L.subtype := by
      apply MonoidHom.ext
      intro b
      change h * (b : Q) * h⁻¹ = h * (b : Q) * h⁻¹
      rfl
    have hLmap : (XL ⊔ XL.map (MulAut.conj hl).toMonoidHom).map L.subtype =
        X ⊔ X.map (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map, hcomp]
    have hLeq : L = X ⊔ X.map (MulAut.conj h).toMonoidHom := by
      calc L = (⊤ : Subgroup ↥L).map L.subtype := by
              rw [Subgroup.map_top, Subgroup.range_subtype]
        _ = (XL ⊔ XL.map (MulAut.conj hl).toMonoidHom).map L.subtype := by rw [hsupL]
        _ = X ⊔ X.map (MulAut.conj h).toMonoidHom := hLmap
    exact hLeq.le
  have hbad : ∃ g ∈ L, Even (orderOf (z * (g * z * g⁻¹))) ∧
      2 < orderOf (z * (g * z * g⁻¹)) := by
    obtain ⟨g₀, hg₀even, hg₀gt⟩ := psp4_exists_bad_pair hodd h7
    let gl : ↥L := e'.symm g₀
    have hgl : e' gl = g₀ := e'.apply_symm_apply g₀
    have hconjL : (gl : Q) * z * (gl : Q)⁻¹ ∈ L := hLn.conj_mem z hzL (gl : Q)
    have hxL : z * ((gl : Q) * z * (gl : Q)⁻¹) ∈ L := L.mul_mem hzL hconjL
    let x : ↥L := ⟨z * ((gl : Q) * z * (gl : Q)⁻¹), hxL⟩
    have hxprod : x = ⟨z, hzL⟩ * (gl * ⟨z, hzL⟩ * gl⁻¹) := Subtype.ext rfl
    have hxeval : e' x = u1 K * (g₀ * u1 K * g₀⁻¹) := by
      rw [hxprod, map_mul, map_mul, map_mul, map_inv, hz'e, hgl]
    have hord : orderOf (z * ((gl : Q) * z * (gl : Q)⁻¹)) =
        orderOf (u1 K * (g₀ * u1 K * g₀⁻¹)) := by
      rw [show z * ((gl : Q) * z * (gl : Q)⁻¹) = (x : Q) from rfl,
        Subgroup.orderOf_coe x, ← hxeval]
      exact (MulEquiv.orderOf_eq e' x).symm
    exact ⟨(gl : Q), gl.2, by rw [hord]; exact hg₀even, by rw [hord]; exact hg₀gt⟩
  exact asch1413_caseI_false hV hρ hLn hC hA hAe hq hzA hz2 hzL hXL hXz hXperf hCX
    hnorm hgen hbad

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
