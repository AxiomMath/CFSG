module

public import Certificates.Kernel.AutJ2Vtx.ChainFacts
public import Certificates.Kernel.AutJ2Vtx.NormChk
public import CFSG.Certificates.Kernel.SporSch.ChainKCount

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAJC

open CFSG.Quasithin.F112R.St84.AutJ2Model CFSG.ComponentClassification.J2Cover
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.Certificates
open CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu CertificateChecks.KernelAJV CFSG.KS.MulH

theorem le_normalizer_of_conj {G : Type*} [Group G] {S T : Set G} [Finite (Subgroup.closure T)]
    (h : ∀ c ∈ S, ∀ q ∈ T, c * q * c⁻¹ ∈ Subgroup.closure T) :
    Subgroup.closure S ≤ Subgroup.normalizer (Subgroup.closure T : Set G) := by
  refine (Subgroup.closure_le _).2 fun c hc => ?_
  set K := Subgroup.closure T
  have hle : K.map (MulAut.conj c).toMonoidHom ≤ K := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨q, hq, rfl⟩
    exact h c hc q hq
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have heq : K.map (MulAut.conj c).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective hinj])
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, e⟩ := hx
    have : y = x := hinj e
    rwa [← this]

theorem img_inv_tt {k : Nat} (hk : k < 22) :
    imageList (tp 315 (tt k))⁻¹ = (unpack 315 9 (AJI k)).toList := by
  obtain ⟨c1, c2, c3⟩ := inv_spec hk
  have hr := rep_invT (rep_tp (permOK_unpack c1 c3)) (by
    rw [invT_unpack (lt_of_canonK c2) c3]
    exact invOK_unpack c1 c2 c3)
  rw [invT_unpack (lt_of_canonK c2) c3, tabT_eq_tabP] at hr
  exact CFSG.KC.KGC31P.imageList_of_rep c2 hr

theorem img_cj {c q : Nat} (hc : c < 22) (hq : q < 22) :
    imageList (tp 315 (tt c) * tp 315 (tt q) * (tp 315 (tt c))⁻¹) =
      (unpack 315 9 (cjK c q)).toList := by
  have hn : (315 : Nat) < 2 ^ 32 := by norm_num
  exact CFSG.KC.KGC31P.imageList_of_prep (CFSG.KS.Raw.Orb.prep_pcomp hn (CFSG.KS.Raw.Orb.prep_pcomp hn
    (prep_of_imageList (img_tt hc)) (prep_of_imageList (img_tt hq)))
    (prep_of_imageList (img_inv_tt hc)))

theorem canon_cj {c q : Nat} (hc : c < 22) (hq : q < 22) :
    canonK 315 9 (mask 9) (315 * 9) (cjK c q) = true :=
  CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp (inv_spec hc).1 (inv_spec hq).1)
    (inv_spec hc).2.1

theorem conj_mem {cs qs : List Nat} (hcs : ∀ c ∈ cs, c < 22) (hqs : ∀ q ∈ qs, q < 22)
    {words : List (List Int)} {k : Nat} {bv : Vector (Fin 315) k} (hbs : bv.toList.Nodup)
    {PS PSI LR TR TRI : Nat → Nat} {kS BP : Nat}
    (hQ : ChainK 315 9 (gensOf qs) words bv PS PSI LR TR TRI kS BP 1 315)
    (hk : (List.range cs.length).all (fun a => (List.range qs.length).all fun b =>
      siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) LR TRI BP k 0
        (cjK (cs.getD a 0) (qs.getD b 0))) = true) :
    ∀ c ∈ {g | g ∈ gensOf cs}, ∀ q ∈ {g | g ∈ gensOf qs},
      c * q * c⁻¹ ∈ Subgroup.closure {g | g ∈ gensOf qs} := by
  intro c hc q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have hs := List.all_eq_true.1 (List.all_eq_true.1 hk i (List.mem_range.2 hi)) j
    (List.mem_range.2 hj)
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hs
  have hc' := hcs _ (List.getElem_mem hi)
  have hq' := hqs _ (List.getElem_mem hj)
  have h := chainK_sift (by norm_num) hbs hQ (img_cj hc' hq') (canon_cj hc' hq') hs
  rw [RawSchreierDatum.sift_eq_true_iff_mem_original _ (chainK_valid hQ (by norm_num) hbs),
    certificate_originalSubgroup] at h
  exact h

theorem finite_genOf (ks : List Nat) : Finite (Subgroup.closure {g | g ∈ gensOf ks}) :=
  Subtype.finite

theorem norm_W : genOf 315 ([0, 1, 2, 6].map tt) ≤
    Subgroup.normalizer (genOf 315 ([8, 9, 10, 11].map tt) : Set (Equiv.Perm (Fin 315))) := by
  rw [genOf_eq, genOf_eq]
  have := finite_genOf [8, 9, 10, 11]
  exact le_normalizer_of_conj (conj_mem (by decide) (by decide) (by decide) chQ2 kNmW)

theorem norm_X1 : genOf 315 ([0, 1, 2, 7].map tt) ≤
    Subgroup.normalizer (genOf 315 ([14, 15, 16, 17].map tt) : Set (Equiv.Perm (Fin 315))) := by
  rw [genOf_eq, genOf_eq]
  have := finite_genOf [14, 15, 16, 17]
  exact le_normalizer_of_conj (conj_mem (by decide) (by decide) (by decide) chQ1 kNmX1)

end CertificateChecks.KernelAJC

end
