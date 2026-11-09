module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW3
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicWitData

public section

namespace CertificateChecks.KernelCensus.M24C

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem inXL_sub_map {n : ℕ} {f : ℕ → Array ℕ} {X : Array ℕ} (ks : List ℕ)
    (hk : ks.all (fun k => decide (k < X.size)) = true) (a : Array ℕ)
    (ha : inXL n ((ks.map fun k => f X[k]!).toArray) a = true) : inXL n (X.map f) a = true := by
  unfold inXL at ha ⊢
  obtain ⟨y, hy, he⟩ := List.any_eq_true.1 ha
  have hy' : y ∈ ks.map (fun k => f X[k]!) := by simpa using hy
  obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hy'
  have hlt : k < X.size := by simpa using List.all_eq_true.1 hk k hk'
  refine List.any_eq_true.2 ⟨f X[k], ?_, ?_⟩
  · rw [Array.toList_map]
    exact List.mem_map.2 ⟨X[k], Array.getElem_mem_toList hlt, rfl⟩
  · rw [getElem!_pos X k hlt] at he
    exact he

theorem witOKW3_closing_mono {n : ℕ} {ps : List ℕ} {inX inX' outX : Array ℕ → Bool}
    {allowPW allowInX allowU : Bool} {basis : Array (Array ℕ)} {cE : ArrCert}
    {cs : Array ArrCert} {pf : PerfW} {cl : ClosW} {w : Wit} {s t : ℕ} {c : Array ℕ} {kc v : ℕ}
    {gens : List (List CFac × ℕ)} {comms : List (ℕ × ℕ)}
    (hX : ∀ a, inX a = true → inX' a = true) (hw : w = .closing s t c kc v gens comms)
    (h : witOKW3 n ps inX outX allowPW allowInX allowU basis cE cs pf cl w = true) :
    witOKW3 n ps inX' outX allowPW allowInX allowU basis cE cs pf cl w = true := by
  subst hw
  have hok : ∀ f : CFac, CFac.okK n inX basis f = true → CFac.okK n inX' basis f = true := by
    intro f hf
    simp only [CFac.okK, Bool.and_eq_true] at hf ⊢
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hf
    exact ⟨⟨⟨⟨h1, h2⟩, hX _ h3⟩, hX _ h4⟩, h5⟩
  have hg : gens.all (fun l => l.1.all (CFac.okK n inX basis)) = true →
      gens.all (fun l => l.1.all (CFac.okK n inX' basis)) = true := by
    intro hL
    simp only [List.all_eq_true] at hL ⊢
    exact fun l hl f hf => hok f (hL l hl f hf)
  simp only [witOKW3, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩, h16⟩, h17⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hX _ h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, hg h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩

end CertificateChecks.KernelCensus.M24C

end
