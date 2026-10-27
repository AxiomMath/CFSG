module

public import CFSG.Monster.GMS.U6Odd

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem fourAOddOrder_of_eightOne
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (h : EightOneOddOrder a z₀) : FourAOddOrder a z₀ := by
  intro b y z hb hy hz M hM hodd
  obtain ⟨b₀, z', u', φ, C⟩ :=
    exists_tableVICtx I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hb hy
  obtain ⟨hw1, hwB, hww, hbQ, -, hyQ⟩ := C.k3_data hz.1 (C.cond_to_orbit hz.1 hz.2)
  have hMb : ∀ m ∈ M, m * b = b * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.1 (hM hm).1.1
  have hMz : ∀ m ∈ M, m * z = z * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.1 (hM hm).2
  have hMw : ∀ m ∈ M, m * ((b * z) * (b * z)) = ((b * z) * (b * z)) * m := by
    intro m hm
    have hbz : Commute m (b * z) :=
      (show Commute m b from hMb m hm).mul_right (show Commute m z from hMz m hm)
    exact (hbz.mul_right hbz).eq
  generalize (b * z) * (b * z) = w at hw1 hwB hww hbQ hyQ hMw
  have hbw : b * w = w * b :=
    Subgroup.mem_centralizer_singleton_iff.1 (leechQ_le_centralizer w hbQ)
  have hyw : y * w = w * y :=
    Subgroup.mem_centralizer_singleton_iff.1 (leechQ_le_centralizer w hyQ)
  have hl : IsLineTriple a b y := ⟨hb, hy.1, hy.2⟩
  have hcount : twoBCount z₀ b y w = 1 := by
    rw [S365.twoBCount_eq_of_twoB I hG hl hwB hbw hyw]
    simp only [hbQ, hyQ, Subgroup.mul_mem _ hbQ hyQ, ↓reduceIte, add_zero]
  have hne : ∀ c : G, IsConj a c → w ≠ c := fun c hc hwc =>
    hG.not_isConj (hc.trans (hwc ▸ hwB).symm)
  have he : IsEightExt b y w :=
    ⟨hww, hbw.symm, hyw.symm, hw1, hne b hb, hne y hy.1, hne (b * y) hy.2⟩
  exact h b y w hl he hcount M
    (fun m hm => ⟨(hM hm).1, Subgroup.mem_centralizer_singleton_iff.2 (hMw m hm)⟩) hodd

theorem fourAOddOrder_of_leech
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    FourAOddOrder a z₀ :=
  fourAOddOrder_of_eightOne I hG (U6Odd.eightOneOddOrder_of I hG)

end CFSG.Monster.GMS
