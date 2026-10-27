module

public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictDefs
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictJData
public import Certificates.Certificate7930
public import Certificates.Certificate7931
public import Certificates.Certificate7932

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CFSG.J4Tree.VerdictJ (Ctx NPData FData)

theorem burnsideJ4NP_mem_normalizer_closure {S : Set J} {s : J}
    (h : ∀ x ∈ S, s * x * s⁻¹ ∈ Subgroup.closure S) :
    s ∈ Subgroup.normalizer ((Subgroup.closure S : Subgroup J) : Set J) := by
  set K := Subgroup.closure S
  have hle : K.map (MulAut.conj s).toMonoidHom ≤ K := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : K.map (MulAut.conj s).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [burnsideJ4KW_card_map_conj])
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hle ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : s * z * s⁻¹ = s * y * s⁻¹ := by simpa [MulAut.conj_apply] using hzy
    have : z = y := by simpa using hzy'
    rwa [← this]

@[expose] noncomputable def burnsideJ4NP_coordSub (L : List (ℕ × ℕ)) : Subgroup J :=
  Subgroup.closure {g | g ∈ L.map burnsideJ4NP_treeElt}

@[expose] noncomputable def burnsideJ4NP_maskElt (L : List (ℕ × ℕ)) (m : ℕ) : J :=
  (List.range L.length).foldl
    (fun acc l => if m.testBit l then acc * burnsideJ4NP_treeElt (L.getD l (0, 0)) else acc) 1

theorem burnsideJ4NP_getD_mem {L : List (ℕ × ℕ)} {i : ℕ} (hi : i < L.length) :
    L.getD i (0, 0) ∈ L := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem burnsideJ4NP_verdictW_vjT3 :
    ∀ d ∈ burnsideJ4NP_vjT3, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv d.node) := by
  intro d hd
  have e : burnsideJ4NP_vjT3.map NPData.node = burnsideJ4NP_vjT3Ids := rfl
  obtain ⟨g, hg⟩ := Certificates.certificate7930 d.node (e ▸ List.mem_map_of_mem hd)
  exact burnsideJ4NP_verdictW_np hg

theorem burnsideJ4NP_verdictW_vjH :
    ∀ d ∈ burnsideJ4NP_vjH, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv d.node) := by
  intro d hd
  have e : burnsideJ4NP_vjH.map NPData.node = burnsideJ4NP_vjHIds := rfl
  obtain ⟨g, hg⟩ := Certificates.certificate7931 d.node (e ▸ List.mem_map_of_mem hd)
  exact burnsideJ4NP_verdictW_np hg

theorem burnsideJ4NP_verdictW_vjF :
    ∀ d ∈ burnsideJ4NP_vjF, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv d.node) := by
  intro d hd
  rw [burnsideJ4NP_vjF, List.mem_singleton] at hd
  subst hd
  obtain ⟨x, hx⟩ := Certificates.certificate7932
  exact burnsideJ4NP_verdictW_F hx

end CFSG.ASVolI
