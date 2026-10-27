module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbrLabel
public import CFSG.LocalAnalysis.StandardType.GGMultTableCl
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGK1ScMain
import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem ggMultDatumA_trivial_orbit {p nf d : ℕ} {tw : Bool} {mm : List ℕ}
    (htriv : (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)) {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA p nf d tw mm).orbits) :
    o.lab.n = nf ∧ (d = 1 → o.lab.tag = .A) ∧
      (d = 2 → o.lab.tag = .twA ∨ (o.lab.tag = .A ∧ o.lab.rank = 1)) := by
  simp only [ggMultDatumA] at ho
  rw [if_pos htriv] at ho
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at ho
  obtain ⟨j, -, hjo⟩ := ho
  rw [← hjo]
  refine ⟨ggMultBlockA_n _ _ _, ?_, ?_⟩
  · intro hd
    rw [hd]
    simp [ggMultBlockA]
  · intro hd
    rw [hd]
    unfold ggMultBlockA
    rw [if_neg (by decide : ¬ (2 : ℕ) = 1)]
    split_ifs <;> simp

theorem ggMultValidCl_linear_orbit {lab : LargeEvenLabel} {p : ℕ} {D : GGKacDatum}
    (hV : GGMultValidCl lab p D) (htag : lab.tag = .A) (hd : p ∣ 2 ^ lab.n - 1)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) :
    o.lab.n = lab.n ∧ o.lab.tag = .A := by
  obtain ⟨T, tw, m, hlab, hDmem⟩ := hV
  rcases lab with ⟨tag, r, e⟩
  have htag' : tag = .A := htag
  subst tag
  simp only [ggKacTypeClOfLabel, Option.some.injEq, Prod.mk.injEq] at hlab
  obtain ⟨rfl, rfl, rfl⟩ := hlab
  have hord : ggMultOrd p e ≠ 0 := ggMultTableCl_ord_ne_zero hDmem
  obtain ⟨mm, -, -, -, hDeq⟩ :=
    (mem_ggMultTableCl_A (r := r) (p := p) (n := e) (tw := false) (D := D) hord).mp hDmem
  rw [hDeq] at ho
  have hd1 : ggMultOrd p e = 1 := by
    unfold ggMultOrd
    rw [if_pos hd]
  rw [hd1] at ho
  obtain ⟨hnO, htagO, -⟩ :=
    ggMultDatumA_trivial_orbit (p := p) (nf := e) (d := 1) (tw := false) (mm := mm)
      (Or.inl ⟨rfl, rfl⟩) ho
  exact ⟨hnO, htagO rfl⟩

theorem ggMultValidCl_unitary_orbit {lab : LargeEvenLabel} {p : ℕ} {D : GGKacDatum}
    (hV : GGMultValidCl lab p D) (htag : lab.tag = .twA) (hd : p ∣ 2 ^ lab.n + 1)
    (hnd : ¬ p ∣ 2 ^ lab.n - 1) {o : GGKacOrbit} (ho : o ∈ D.orbits) :
    o.lab.n = lab.n ∧ (o.lab.tag = .twA ∨ (o.lab.tag = .A ∧ o.lab.rank = 1)) := by
  obtain ⟨T, tw, m, hlab, hDmem⟩ := hV
  rcases lab with ⟨tag, r, e⟩
  have htag' : tag = .twA := htag
  subst tag
  simp only [ggKacTypeClOfLabel, Option.some.injEq, Prod.mk.injEq] at hlab
  obtain ⟨rfl, rfl, rfl⟩ := hlab
  have hord : ggMultOrd p e ≠ 0 := ggMultTableCl_ord_ne_zero hDmem
  obtain ⟨mm, -, -, -, hDeq⟩ :=
    (mem_ggMultTableCl_A (r := r) (p := p) (n := e) (tw := true) (D := D) hord).mp hDmem
  rw [hDeq] at ho
  have hd2 : ggMultOrd p e = 2 := by
    unfold ggMultOrd
    rw [if_neg hnd, if_pos hd]
  rw [hd2] at ho
  obtain ⟨hnO, -, htwO⟩ :=
    ggMultDatumA_trivial_orbit (p := p) (nf := e) (d := 2) (tw := true) (mm := mm)
      (Or.inr ⟨rfl, rfl⟩) ho
  exact ⟨hnO, htwO rfl⟩

private theorem ggLabelIso_perm_eq {lab : LargeEvenLabel} {t : LargeEvenLieTag} {m f : ℕ}
    (hiso : GGLabelIso lab ⟨t, m, f⟩) (ht : t = .A ∨ t = .twA)
    (hlab : lab.tag = .A ∨ lab.tag = .twA ∨ (lab.tag = .A ∧ lab.rank = 1)) :
    lab = ⟨t, m, f⟩ := by
  obtain ⟨tag, rnk, nf⟩ := lab
  have hlab' : tag = .A ∨ tag = .twA ∨ (tag = .A ∧ rnk = 1) := hlab
  rcases hiso with h | ⟨h1, h2, -, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · have htB : t = .B ∨ t = .C := h2
    rcases htB with hB | hC
    · rcases ht with hA | hA <;> rw [hA] at hB <;> exact absurd hB (by decide)
    · rcases ht with hA | hA <;> rw [hA] at hC <;> exact absurd hC (by decide)
  · have hD : tag = .D := congrArg LargeEvenLabel.tag h1
    rcases hlab' with h | h | ⟨h, -⟩ <;> rw [h] at hD <;> exact absurd hD (by decide)
  · have hD : t = .D := congrArg LargeEvenLabel.tag h2
    rcases ht with h | h <;> rw [h] at hD <;> exact absurd hD (by decide)
  · have hD : tag = .twD := congrArg LargeEvenLabel.tag h1
    rcases hlab' with h | h | ⟨h, -⟩ <;> rw [h] at hD <;> exact absurd hD (by decide)
  · have hD : t = .twD := congrArg LargeEvenLabel.tag h2
    rcases ht with h | h <;> rw [h] at hD <;> exact absurd hD (by decide)
  · have hD : tag = .twD := congrArg LargeEvenLabel.tag h1
    rcases hlab' with h | h | ⟨h, -⟩ <;> rw [h] at hD <;> exact absurd hD (by decide)
  · have hD : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases ht with h | h <;> rw [h] at hD <;> exact absurd hD (by decide)

section Label


theorem GGSecFiveRouteCfg.permNbr_field_of_generic {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n) {K : Subgroup G}
    (hK𝒦 : K ∈ 𝒦) {labK : LargeEvenLabel} (hΛK : LargeEvenInLambda2 labK)
    (hhasK : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K)) (hpermK : GGSecFiveBPermLabel n p labK)
    (hgen : ¬ p ∣ n) {t : LargeEvenLieTag} {e : ℕ} (ht : t = .A ∨ t = .twA)
    (hΛJ : LargeEvenInLambda2 ⟨t, n - 2, e⟩)
    (hJ : GGHasLabel ⟨t, n - 2, e⟩ (↥J ⧸ Subgroup.center ↥J)) :
    labK.tag = t ∧ labK.n = e := by
  have hI3 : GGNbrSubcomponentInput := ggNbrSubcomponentInput_proved
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
  have hInnK : GGInnerDiagOn Bs K := hR.1.2.2.1.2 y K hnb
  have hT : GGThmIHyp p B x L := hcfg.1
  have hSS : LargeEvenSStar p B x L := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hx : x ∈ B := hSS.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hx
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hJK : J ≤ K := ggNbrK_J_le_K hI3 hcfg hnb
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSS hDJ hnb hJK
  have htagK : labK.tag = .A ∨ labK.tag = .twA :=
    hpermK.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hrankK : labK.rank = n - 1 :=
    hpermK.elim (fun h => h.2.1) (fun h => h.2.1)
  have hdvdK : p ∣ 2 ^ labK.n - 1 ∨ p ∣ 2 ^ labK.n + 1 :=
    hpermK.elim (fun h => Or.inl h.2.2) (fun h => Or.inr h.2.2)
  have hgenK : GGKacGenericCl labK p := by
    have hrankn : labK.rank + 1 = n := by rw [hrankK]; omega
    have hpn : ¬ p ∣ labK.rank + 1 := fun h => hgen (hrankn ▸ h)
    refine ⟨hp, hp2, hdvdK, ?_, fun h => hpn h.2.1, fun h => hpn h.2.1⟩
    rcases htagK with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨R, hRgrp, θ, I, F, hN, hind, hPk⟩ :=
    ggNbrK_datum_of_label hRig hInnK hΛK hhasK (ggK0Main_cl p labK hΛK hgenK)
  let : Group R := hRgrp
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hN hxBs
  let ψ : ↥K →* R :=
    (θ : ↥K ⧸ Subgroup.center ↥K →* R).comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hψsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥K := by
    intro l hl
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : ↥K ⧸ Subgroup.center ↥K) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  let σ : MulAut ↥K := K.normalizerMonoidHom ⟨x, hxN⟩
  have hx1 : x ^ p = 1 := hBel.2 x hx
  have hσp : σ ^ p = 1 := by
    dsimp only [σ]
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hx1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind x⁻¹ (Bs.inv_mem hxBs)
  have hine : ∃ φ ∈ I, ∀ l : ↥K, φ (ψ l) = ψ (σ l) := by
    refine ⟨φ, hφI, fun l => hφ l (σ l) ?_⟩
    show ((σ l : ↥K) : G) = x⁻¹⁻¹ * (l : G) * x⁻¹
    dsimp only [σ]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hJcomp : IsComponentOf (J.subgroupOf K) (ggFixSub σ) :=
    ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  obtain ⟨D, hValid, hcompA, -, -, -⟩ :=
    hPk ↥K ψ hψsurj hψker hInnK.1 σ hσp hine
  obtain ⟨o, ho, hqs, hndvd, hΛo, hhasO⟩ := hcompA (J.subgroupOf K) hJcomp
  have hhasO' : GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
      (Subgroup.map_center_eq _)) hhasO
  have hiso : GGLabelIso o.lab ⟨t, n - 2, e⟩ :=
    hRig o.lab ⟨t, n - 2, e⟩ (↥J ⧸ Subgroup.center ↥J) hΛo hΛJ hhasO' hJ
  rcases hpermK with ⟨htagA, -, hdvdA⟩ | ⟨htagU, -, hdvdU⟩
  · have hlin := ggMultValidCl_linear_orbit hValid htagA hdvdA ho
    have heq := ggLabelIso_perm_eq hiso ht (Or.inl hlin.2)
    have hOt : o.lab.tag = t := congrArg LargeEvenLabel.tag heq
    have hOn : o.lab.n = e := congrArg LargeEvenLabel.n heq
    refine ⟨?_, hlin.1.symm.trans hOn⟩
    rw [htagA, ← hlin.2]
    exact hOt
  · have hnd : ¬ p ∣ 2 ^ labK.n - 1 := ggNbrK_not_dvd_sub_one hp hp2 hdvdU
    have hun := ggMultValidCl_unitary_orbit hValid htagU hdvdU hnd ho
    have heq := ggLabelIso_perm_eq hiso ht (by
      rcases hun.2 with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
    have hOt : o.lab.tag = t := congrArg LargeEvenLabel.tag heq
    have hOn : o.lab.n = e := congrArg LargeEvenLabel.n heq
    have htwA : o.lab.tag = .twA := by
      rcases hun.2 with h | ⟨-, hr⟩
      · exact h
      · rw [heq] at hr
        exfalso
        have h1 : n - 2 = 1 := by simpa using hr
        omega
    refine ⟨?_, hun.1.symm.trans hOn⟩
    rw [htagU, ← htwA]
    exact hOt

end Label

end CFSG.StandardType

end
