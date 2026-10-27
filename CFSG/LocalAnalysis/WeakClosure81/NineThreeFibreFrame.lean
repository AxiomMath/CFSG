module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreTrans
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreIndep
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIWChoice

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}
  {ρ : ↥K →* Equiv.Perm (ZMod p)}

theorem nine3_dbar_sq (hc : Nine3Choice V T A K S X p g x) {d : Nine3Hbar V K}
    (hd : d ∈ Nine3Dbar V K) : d * d = 1 := by
  obtain ⟨U, hU, u, hu, huR, hd_eq⟩ := hd
  rw [← hd_eq]
  obtain ⟨g, rfl, -, -⟩ := mem_omegaSet.mp hU.1
  have hsq : (u : G) * (u : G) = 1 := by
    have h := (isElemAbelian_conjSubgroup' hc.core.hyp7.1 g).2 (u : G) hu
    simpa [pow_two] using h
  have hsqH : (u * u : ↥(nineH V K)) = 1 := Subtype.ext (by simpa using hsq)
  rw [← QuotientGroup.mk_mul, hsqH, QuotientGroup.mk_one]

theorem nine3_dbar_conj (hc : Nine3Choice V T A K S X p g x) {d : Nine3Hbar V K}
    (hd : d ∈ Nine3Dbar V K) (γ : Nine3Hbar V K) : γ * d * γ⁻¹ ∈ Nine3Dbar V K := by
  obtain ⟨U, hU, u, hu, huR, hd_eq⟩ := hd
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective γ
  rw [← hd_eq]
  have hhK : (h : G) ∈ K := Nine3Choice.nineH_le_K h.2
  refine ⟨conjSubgroup U ((h : G)⁻¹), conjSubgroup_mem_omegaIn hU (K.inv_mem hhK), ?_⟩
  refine ⟨⟨(h : G) * (u : G) * (h : G)⁻¹, ?_⟩, ?_, ?_, ?_⟩
  · exact (nineH V K).mul_mem ((nineH V K).mul_mem h.2 u.2) ((nineH V K).inv_mem h.2)
  · rw [mem_conjSubgroup_iff]
    have hcancel : (h : G)⁻¹ * ((h : G) * (u : G) * (h : G)⁻¹) * ((h : G)⁻¹)⁻¹ = (u : G) := by
      group
    rw [hcancel]
    exact hu
  · intro hR
    exact huR ((Nine3Core.mem_pCoreOf_conj_iff K hhK).mpr hR)
  · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem nine3_dbar_gen (hc : Nine3Choice V T A K S X p g x) :
    Subgroup.closure (Nine3Dbar V K) = ⊤ := by
  let N := (nineI V K).subgroupOf (nineH V K)
  let C : Subgroup (Nine3Hbar V K) := Subgroup.closure (Nine3Dbar V K)
  have hgen : nineH V K ≤ (C.comap (QuotientGroup.mk' N)).map (nineH V K).subtype := by
    refine iSup₂_le fun U hU => ?_
    intro x hx
    have hxH : x ∈ nineH V K := (le_iSup₂_of_le U hU le_rfl : U ≤ nineH V K) hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    by_cases hxR : x ∈ pCoreOf 2 K
    · have hxI : x ∈ nineI V K :=
        (le_iSup₂_of_le U hU le_rfl : U ⊓ pCoreOf 2 K ≤ nineI V K) ⟨hx, hxR⟩
      have hxN : (⟨x, hxH⟩ : ↥(nineH V K)) ∈ N := by
        rw [Subgroup.mem_subgroupOf]
        exact hxI
      have hone : QuotientGroup.mk' N ⟨x, hxH⟩ = 1 := by
        simpa only [QuotientGroup.mk'_apply] using
          (QuotientGroup.eq_one_iff (N := N) ⟨x, hxH⟩).mpr hxN
      rw [hone]
      exact C.one_mem
    · exact Subgroup.subset_closure ⟨U, hU, ⟨x, hxH⟩, hx, hxR, rfl⟩
  rw [eq_top_iff]
  intro y _
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
  have h := hgen u.2
  rw [Subgroup.mem_map] at h
  obtain ⟨a, haC, ha_eq⟩ := h
  have hau : a = u := Subtype.ext ha_eq
  rw [hau, Subgroup.mem_comap] at haC
  simpa only [QuotientGroup.mk'_apply] using haC

theorem nine3_dbar_refl (hc : Nine3Choice V T A K S X p g x) (hρ : Nine3FibreAct K S p x ρ)
    {d : Nine3Hbar V K} (hd : d ∈ Nine3Dbar V K) :
    ∃ c : ZMod p, nine3Pi V K ρ hρ.le_ker d = zmodRefl p c := by
  obtain ⟨U, hU, u, hu, huR, hd_eq⟩ := hd
  obtain ⟨c, hc⟩ := nine3_exists_fib hc hρ hU
  exact ⟨c, by rw [← hd_eq]; exact (nine3_mk_mem_dbar hU hρ.le_ker hc hu huR).2⟩

private lemma nine3_two_ne_zero_frame {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hc
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hc
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

private lemma nine3_zmodRefl_conj_frame (p : ℕ) (s a : ZMod p) :
    zmodRefl p s * zmodRefl p a * zmodRefl p s = zmodRefl p (2 * s - a) := by
  ext i
  simp only [zmodRefl, Equiv.Perm.mul_apply, Equiv.subLeft_apply]
  ring

private theorem nine3_exists_notMem_pCoreOf_of_mem_omegaIn (hc : Nine3Choice V T A K S X p g x)
    {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    ∃ u : ↥(nineH V K), (u : G) ∈ U ∧ (u : G) ∉ pCoreOf 2 K := by
  have hleH : U ≤ nineH V K := le_iSup₂_of_le U hU le_rfl
  have hex : ∃ u : G, u ∈ U ∧ u ∉ pCoreOf 2 K := by
    by_contra hcon
    have hle : U ≤ pCoreOf 2 K := by
      intro x hx
      by_contra hxR
      exact hcon ⟨x, hx, hxR⟩
    have hrel := nine3_relIndex_of_mem_omegaIn hc hU
    have hinf : U ⊓ pCoreOf 2 K = U := inf_eq_left.mpr hle
    rw [hinf, Subgroup.relIndex_self] at hrel
    omega
  obtain ⟨u, hu, huR⟩ := hex
  exact ⟨⟨u, hleH hu⟩, hu, huR⟩

private theorem nine3_list_prod_mem_frame {W : Subgroup G} (Ls : List (Subgroup G))
    (bs : List G) (hle : ∀ B ∈ Ls, B ≤ W)
    (hb : List.Forall₂ (fun B b => b ∈ B) Ls bs) : bs.prod ∈ W := by
  induction Ls generalizing bs with
  | nil =>
    rw [List.forall₂_nil_left_iff.mp hb]
    simpa using W.one_mem
  | cons B Ls' ih =>
    obtain ⟨b, bs', hbhead, hbtail, rfl⟩ := List.forall₂_cons_left_iff.mp hb
    exact W.mul_mem (hle B (by simp) hbhead)
      (ih bs' (fun B' hB' => hle B' (List.mem_cons_of_mem B hB')) hbtail)

private theorem nine3_fibre_zero_repr (hc : Nine3Choice V T A K S X p g x)
    (hρ : Nine3FibreAct K S p x ρ) :
    ∀ (l : List (Nine3Hbar V K)), l.Nodup →
      (∀ d ∈ l, d ∈ Nine3Dbar V K ∧ nine3Pi V K ρ hρ.le_ker d = zmodRefl p 0) →
      ∃ (Ls : List (Subgroup G)) (bs : List ↥(nineH V K)),
        Ls.Nodup ∧ (∀ B ∈ Ls, B ∈ nineOmegaIn V K S) ∧
        List.Forall₂ (fun (B : Subgroup G) (b : ↥(nineH V K)) =>
          (b : G) ∈ B ∧ (b : G) ∉ pCoreOf 2 K) Ls bs ∧
        l = bs.map (QuotientGroup.mk' ((nineI V K).subgroupOf (nineH V K))) := by
  intro l
  induction l with
  | nil =>
    intro _ _
    exact ⟨[], [], List.nodup_nil, by simp, List.Forall₂.nil, by simp⟩
  | cons d l' ih =>
    intro hl hmem
    have hd : d ∈ Nine3Dbar V K ∧ nine3Pi V K ρ hρ.le_ker d = zmodRefl p 0 := hmem d (by simp)
    obtain ⟨U, hU, hUc, u, hu, huR, hdu⟩ := nine3_dbar_over hc hρ hd.1 hd.2
    have hUS : U ≤ S := (nine3_fib_zero_iff hc hρ hU).mp hUc
    have hUΩ : U ∈ nineOmegaIn V K S := ⟨hU.1, hUS⟩
    have hl' : l'.Nodup := (List.nodup_cons.mp hl).2
    have hmem' : ∀ e ∈ l', e ∈ Nine3Dbar V K ∧
        nine3Pi V K ρ hρ.le_ker e = zmodRefl p 0 := fun e he => hmem e (List.mem_cons_of_mem d he)
    obtain ⟨Ls', bs', hLs', hmemLs', hb', hl'_eq⟩ := ih hl' hmem'
    have hUnotMem : U ∉ Ls' := by
      intro hUmem
      obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp ⟨U, hUmem, rfl⟩
      have hlen : Ls'.length = bs'.length := List.Forall₂.length_eq hb'
      have hj : i.val < bs'.length := by rw [← hlen]; exact i.isLt
      have hrel := hb'.get (i := i.val) i.isLt hj
      have hb'mem : bs'.get ⟨i.val, hj⟩ ∈ bs' := List.get_mem bs' ⟨i.val, hj⟩
      have hb'U : ((bs'.get ⟨i.val, hj⟩ : ↥(nineH V K)) : G) ∈ U := by
        have h := hrel.1
        rwa [← hi] at h
      have hb'R : ((bs'.get ⟨i.val, hj⟩ : ↥(nineH V K)) : G) ∉ pCoreOf 2 K := hrel.2
      have hmkeq : (QuotientGroup.mk (bs'.get ⟨i.val, hj⟩) : Nine3Hbar V K) = d := by
        rw [← nine3_mk_eq_of_mem hc hU hu hb'U huR hb'R, hdu]
      have hdmem : d ∈ l' := by
        rw [hl'_eq, ← hmkeq]
        simpa only [QuotientGroup.mk'_apply] using
          List.mem_map_of_mem (f := QuotientGroup.mk' ((nineI V K).subgroupOf (nineH V K))) hb'mem
      exact (List.nodup_cons.mp hl).1 hdmem
    refine ⟨U :: Ls', u :: bs', ?_, ?_, ?_, ?_⟩
    · exact List.nodup_cons.mpr ⟨hUnotMem, hLs'⟩
    · intro B hB
      rcases List.mem_cons.mp hB with rfl | hB'
      · exact hUΩ
      · exact hmemLs' B hB'
    · exact List.Forall₂.cons ⟨hu, huR⟩ hb'
    · rw [List.map_cons, QuotientGroup.mk'_apply, hdu, ← hl'_eq]

theorem nine3_dbar_card (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    (hρ : Nine3FibreAct K S p x ρ) (c : ZMod p) :
    Nat.card {d : Nine3Hbar V K // d ∈ Nine3Dbar V K ∧
      nine3Pi V K ρ hρ.le_ker d = zmodRefl p c} = Nat.card ↥(nineOmegaIn V K S) := by
  classical
  let Om : ZMod p → Set (Subgroup G) :=
    fun e => {U | U ∈ omegaIn V K (nineE V K) ∧ Nine3Fib K p ρ U e}
  have hOm0 : Om 0 = nineOmegaIn V K S := by
    ext U
    constructor
    · rintro ⟨hU, hfib⟩
      exact ⟨hU.1, (nine3_fib_zero_iff hc hρ hU).mp hfib⟩
    · rintro ⟨hUset, hUS⟩
      have hU : U ∈ omegaIn V K (nineE V K) := ⟨hUset, hUS.trans hc.core.S_le_K⟩
      exact ⟨hU, (nine3_fib_zero_iff hc hρ hU).mpr hUS⟩
  have hcard_b : Nat.card ↥(Om c) = Nat.card ↥(Om 0) := by
    obtain ⟨k, -, -, hk⟩ := nine3_exists_translation hc hρ (-c)
    have hfwd : ∀ U ∈ Om 0, conjSubgroup U (k : G) ∈ Om c := by
      intro U hU
      exact ⟨conjSubgroup_mem_omegaIn hU.1 k.2,
        by simpa using nine3_fib_conj (ρ := ρ) hU.2 hk⟩
    have hbwd : ∀ U ∈ Om c, conjSubgroup U ((k⁻¹ : ↥K) : G) ∈ Om 0 := by
      intro U hU
      have hkinv : ∀ i : ZMod p, ρ (k⁻¹) i = i + c := by
        intro i
        rw [map_inv, Equiv.Perm.inv_eq_iff_eq, hk]
        ring
      exact ⟨conjSubgroup_mem_omegaIn hU.1 (K.inv_mem k.2),
        by simpa using nine3_fib_conj (ρ := ρ) hU.2 hkinv⟩
    exact Nat.card_congr
      { toFun := fun U => ⟨conjSubgroup U.1 ((k⁻¹ : ↥K) : G), hbwd U.1 U.2⟩
        invFun := fun U => ⟨conjSubgroup U.1 (k : G), hfwd U.1 U.2⟩
        left_inv := by
          intro U
          apply Subtype.ext
          show conjSubgroup (conjSubgroup U.1 ((k⁻¹ : ↥K) : G)) (k : G) = U.1
          rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
          have h1 : ((k⁻¹ : ↥K) : G) * (k : G) = 1 := by
            rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
          rw [h1, CFSG.Quasithin.conjSubgroup_one]
        right_inv := by
          intro U
          apply Subtype.ext
          show conjSubgroup (conjSubgroup U.1 (k : G)) ((k⁻¹ : ↥K) : G) = U.1
          rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
          have h1 : (k : G) * ((k⁻¹ : ↥K) : G) = 1 := by
            rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
          rw [h1, CFSG.Quasithin.conjSubgroup_one] }
  have hcard_c : Nat.card {d : Nine3Hbar V K // d ∈ Nine3Dbar V K ∧
      nine3Pi V K ρ hρ.le_ker d = zmodRefl p c} = Nat.card ↥(Om c) := by
    have hexu : ∀ U : ↥(Om c), ∃ u : ↥(nineH V K), (u : G) ∈ U.1 ∧ (u : G) ∉ pCoreOf 2 K :=
      fun U => nine3_exists_notMem_pCoreOf_of_mem_omegaIn hc U.2.1
    choose uU huU huUR using hexu
    let φ : ↥(Om c) → {d : Nine3Hbar V K // d ∈ Nine3Dbar V K ∧
        nine3Pi V K ρ hρ.le_ker d = zmodRefl p c} :=
      fun U => ⟨QuotientGroup.mk (uU U),
        nine3_mk_mem_dbar U.2.1 hρ.le_ker U.2.2 (huU U) (huUR U)⟩
    have hinj : Function.Injective φ := by
      intro U U' h
      apply Subtype.ext
      have hval : (QuotientGroup.mk (uU U) : Nine3Hbar V K) = QuotientGroup.mk (uU U') :=
        congrArg Subtype.val h
      exact nine3_eq_of_mk_eq hc hI U.2.1 U'.2.1 (huU U) (huU U') (huUR U) (huUR U') hval
    have hsurj : Function.Surjective φ := by
      intro d
      obtain ⟨U₀, hU₀, hU₀c, v, hv, hvR, hvd⟩ := nine3_dbar_over hc hρ d.2.1 d.2.2
      refine ⟨⟨U₀, ⟨hU₀, hU₀c⟩⟩, ?_⟩
      apply Subtype.ext
      show (QuotientGroup.mk (uU ⟨U₀, ⟨hU₀, hU₀c⟩⟩) : Nine3Hbar V K) = d.1
      rw [← hvd]
      exact nine3_mk_eq_of_mem hc hU₀ (huU ⟨U₀, ⟨hU₀, hU₀c⟩⟩) hv (huUR ⟨U₀, ⟨hU₀, hU₀c⟩⟩) hvR
    exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm
  rw [hcard_c, hcard_b, hOm0]

theorem nine3_dbar_comm (hc : Nine3Choice V T A K S X p g x) (hρ : Nine3FibreAct K S p x ρ)
    {d e : Nine3Hbar V K} (hd : d ∈ Nine3Dbar V K) (he : e ∈ Nine3Dbar V K)
    (hde : nine3Pi V K ρ hρ.le_ker d = nine3Pi V K ρ hρ.le_ker e) : d * e = e * d := by
  obtain ⟨c, hdc⟩ := nine3_dbar_refl hc hρ hd
  obtain ⟨U, hU, hUc, u, hu, huR, hdu⟩ := nine3_dbar_over hc hρ hd hdc
  obtain ⟨U', hU', hU'c, u', hu', hu'R, heu⟩ := nine3_dbar_over hc hρ he (hde ▸ hdc)
  rw [← hdu, ← heu]
  have hcommG := nine3_fib_comm hc hρ hU hU' hUc hU'c (u : G) hu (u' : G) hu'
  have hcommH : u * u' = u' * u := Subtype.ext (by simpa using hcommG)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcommH]

theorem nine3_dbar_pow (hc : Nine3Choice V T A K S X p g x) (hρ : Nine3FibreAct K S p x ρ)
    {d e : Nine3Hbar V K} (hd : d ∈ Nine3Dbar V K) (he : e ∈ Nine3Dbar V K)
    (hde : nine3Pi V K ρ hρ.le_ker d ≠ nine3Pi V K ρ hρ.le_ker e) : (d * e) ^ p = 1 := by
  obtain ⟨c, hdc⟩ := nine3_dbar_refl hc hρ hd
  obtain ⟨U, hU, hUc, u, hu, huR, hdu⟩ := nine3_dbar_over hc hρ hd hdc
  obtain ⟨c', hdc'⟩ := nine3_dbar_refl hc hρ he
  obtain ⟨U', hU', hU'c', u', hu', hu'R, heu⟩ := nine3_dbar_over hc hρ he hdc'
  have hcc' : c ≠ c' := fun h => hde (by rw [hdc, hdc', h])
  rw [← hdu, ← heu]
  have hpow : ((u : G) * (u' : G)) ^ p = 1 :=
    nine3_fib_pow hc hρ hU hU' hUc hU'c' hcc' (u : G) hu huR (u' : G) hu' hu'R
  have hpowH : (u * u') ^ p = 1 := Subtype.ext (by simpa using hpow)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hpowH, QuotientGroup.mk_one]

theorem nine3_oddFrame (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    (hρ : Nine3FibreAct K S p x ρ) :
    Nine3OddFrame p (Nat.card ↥(nineOmegaIn V K S)) (nine3Pi V K ρ hρ.le_ker)
      (Nine3Dbar V K) where
  sq := fun _ hd => nine3_dbar_sq hc hd
  conj := fun _ hd γ => nine3_dbar_conj hc hd γ
  gen := nine3_dbar_gen hc
  refl := fun _ hd => nine3_dbar_refl hc hρ hd
  card := nine3_dbar_card hc hI hρ
  comm := fun _ hd _ he hde => nine3_dbar_comm hc hρ hd he hde
  pow := fun _ hd _ he hde => nine3_dbar_pow hc hρ hd he hde
  trans := fun a b hab _ hd hda _ he hea => nine3_oddFrame_trans hc hI hρ a b hab hd hda he hea

theorem nine3_fibreIndep (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    (h3 : 3 ≤ Nat.card ↥(nineDelta V S)) (hρ : Nine3FibreAct K S p x ρ) :
    Nine3FibreIndep p (nine3Pi V K ρ hρ.le_ker) (Nine3Dbar V K) := by
  classical
  haveI : Fact p.Prime := ⟨hc.core.hyp.base.prime⟩
  have hzero : ∀ (l : List (Nine3Hbar V K)), l.Nodup → l ≠ [] →
      (∀ d ∈ l, d ∈ Nine3Dbar V K ∧ nine3Pi V K ρ hρ.le_ker d = zmodRefl p 0) →
      l.prod ≠ 1 := by
    intro l hl hne hmem hprod
    obtain ⟨Ls, bs, hLs, hmemLs, hb, hl_eq⟩ := nine3_fibre_zero_repr hc hρ l hl hmem
    let bsG : List G := bs.map (fun b : ↥(nineH V K) => (b : G))
    have hLsne : Ls ≠ [] := by
      intro hLs0
      apply hne
      have hbs0 : bs = [] := List.forall₂_nil_left_iff.mp (hLs0 ▸ hb)
      rw [hl_eq, hbs0]
      rfl
    have hbG' : List.Forall₂ (fun B b => b ∈ B ∧ b ∉ pCoreOf 2 K) Ls bsG :=
      (List.forall₂_map_right_iff).mpr hb
    have hprodN :
        QuotientGroup.mk' ((nineI V K).subgroupOf (nineH V K)) bs.prod = 1 := by
      have hmap :
          (bs.map (QuotientGroup.mk' ((nineI V K).subgroupOf (nineH V K)))).prod = 1 := by
        rw [← hl_eq]
        exact hprod
      rw [← map_list_prod] at hmap
      exact hmap
    have hbsI : (bs.prod : G) ∈ nineI V K := by
      have hbsN : bs.prod ∈ (nineI V K).subgroupOf (nineH V K) :=
        (QuotientGroup.eq_one_iff (N := (nineI V K).subgroupOf (nineH V K)) bs.prod).mp
          (by simpa only [QuotientGroup.mk'_apply] using hprodN)
      exact Subgroup.mem_subgroupOf.mp hbsN
    have hbsW : bsG.prod ∈ nineW V S := by
      have hbW : List.Forall₂ (fun B b => b ∈ B) Ls bsG := hbG'.imp (fun _ _ h => h.1)
      have hleW : ∀ B ∈ Ls, B ≤ nineW V S := fun B hB =>
        le_iSup₂_of_le B (hc.core.mem_nineDelta_iff.mpr (Or.inr (hmemLs B hB))) le_rfl
      exact nine3_list_prod_mem_frame (W := nineW V S) Ls bsG hleW hbW
    have hbsG_eq : bsG.prod = (bs.prod : G) := (map_list_prod (nineH V K).subtype bs).symm
    have hIWmem : bsG.prod ∈ nineI V K ⊓ nineW V S := ⟨by rwa [hbsG_eq], hbsW⟩
    have hW0 : bsG.prod ∈ nineW0 V K S g := by
      have hIW := nine3IW_of_choice hc hI
      rw [hIW] at hIWmem
      exact hIWmem.2
    exact (nine3_prod_notMem_nineW0 hc hI h3 hLs hLsne hmemLs hbG') hW0
  intro c l hl hne hmem
  by_cases hc0 : c = 0
  · rw [hc0] at hmem
    exact hzero l hl hne hmem
  · have h2ne : (2 : ZMod p) ≠ 0 :=
      nine3_two_ne_zero_frame hc.core.hyp.base.prime hc.core.hyp.base.odd
    have h2c : (2 : ZMod p) * (c / (2 : ZMod p)) = c := by
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm (2 : ZMod p) c, mul_assoc,
        mul_inv_cancel₀ h2ne, mul_one]
    obtain ⟨U, hU, hUfib⟩ := nine3_exists_fib_over hc hρ (c / (2 : ZMod p))
    obtain ⟨u, hu, huR⟩ := nine3_exists_notMem_pCoreOf_of_mem_omegaIn hc hU
    let γ : Nine3Hbar V K := QuotientGroup.mk u
    have hγ : γ ∈ Nine3Dbar V K := (nine3_mk_mem_dbar hU hρ.le_ker hUfib hu huR).1
    have hγpi : nine3Pi V K ρ hρ.le_ker γ = zmodRefl p (c / (2 : ZMod p)) :=
      (nine3_mk_mem_dbar hU hρ.le_ker hUfib hu huR).2
    have hγsq : γ * γ = 1 := nine3_dbar_sq hc hγ
    have hγinv : (nine3Pi V K ρ hρ.le_ker γ)⁻¹ = nine3Pi V K ρ hρ.le_ker γ := by
      have h1 : nine3Pi V K ρ hρ.le_ker γ * nine3Pi V K ρ hρ.le_ker γ = 1 := by
        have hmul := map_mul (nine3Pi V K ρ hρ.le_ker) γ γ
        rw [hγsq, map_one] at hmul
        exact hmul.symm
      exact inv_eq_of_mul_eq_one_right h1
    let l' : List (Nine3Hbar V K) := l.map (fun d => γ * d * γ⁻¹)
    have hl' : l'.Nodup := by
      refine List.Nodup.map ?_ hl
      intro a b hab
      have h := congrArg (fun x : Nine3Hbar V K => γ⁻¹ * x * γ) hab
      simpa [mul_assoc] using h
    have hl'ne : l' ≠ [] := by
      intro h
      exact hne (List.map_eq_nil_iff.mp h)
    have hmem' : ∀ d ∈ l', d ∈ Nine3Dbar V K ∧
        nine3Pi V K ρ hρ.le_ker d = zmodRefl p 0 := by
      intro d hd
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
      have he' := hmem e he
      refine ⟨nine3_dbar_conj hc he'.1 γ, ?_⟩
      rw [map_mul, map_mul, map_inv, hγinv, hγpi, he'.2]
      rw [nine3_zmodRefl_conj_frame]
      rw [h2c, sub_self]
    have hl'prod : l'.prod = γ * l.prod * γ⁻¹ := by
      have h : (l.map (MulAut.conj γ)).prod = γ * l.prod * γ⁻¹ := by
        rw [← map_list_prod (MulAut.conj γ) l, MulAut.conj_apply]
      have hmap : l' = l.map (MulAut.conj γ) := by
        simp only [l']
        refine List.map_congr_left ?_
        intro d _
        rw [MulAut.conj_apply]
      rw [hmap, h]
    intro hprod
    exact hzero l' hl' hl'ne hmem'
      (by rw [hl'prod, hprod, mul_one, mul_inv_cancel])

end CFSG.LocalAnalysis.WeakClosure81
