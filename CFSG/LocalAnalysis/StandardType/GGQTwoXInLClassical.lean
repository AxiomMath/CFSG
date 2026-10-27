module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLSplit
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLModelU
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLModelF
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQTwoXInLFrameUnitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting 3 B Bs x L D J → GGQTwoI1 Bs D J → x ∈ L →
    GGQTwoXInLAmbOn (fun t => t = .twA) Bs (ggG0 3 B x L D J) →
    ∃ (n : ℕ) (_ : 3 ∣ n) (_ : 6 ≤ n) (y : G) (K : Subgroup G) (hx : x ∈ Bs) (hy : y ∈ Bs)
      (ι : Additive ↥Bs ≃+ ↥(GGQTwoXInLAug n)), GGNbr 3 B x D J y K ∧
      (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin (n + 1)), σ 0 = 0 ∧
          ∀ (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)),
            ((T v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
              (v : Fin (n + 1) → ZMod 3) (σ i)} ∧
      (ggAutomizer K Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin (n + 1)), σ 1 = 1 ∧
          ∀ (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)),
            ((T v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
              (v : Fin (n + 1) → ZMod 3) (σ i)} ∧
      ((ι (Additive.ofMul ⟨x, hx⟩) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
        (fun i => if i = 0 then 0 else -1) ∧
      ((ι (Additive.ofMul ⟨y, hy⟩) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
        (fun i => if i = 1 then 0 else -1)

@[expose] def GGQTwoXInLFrameFormed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting 3 B Bs x L D J → GGQTwoI1 Bs D J → x ∈ L →
    GGQTwoXInLAmbOn (fun t => t = .B ∨ t = .C ∨ t = .D ∨ t = .twD) Bs (ggG0 3 B x L D J) →
    ∃ (n : ℕ) (_ : 6 ≤ n) (y : G) (K : Subgroup G) (hx : x ∈ Bs) (hy : y ∈ Bs)
      (ι : Additive ↥Bs ≃+ (Fin n → ZMod 3)), GGNbr 3 B x D J y K ∧
      (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
          T v i = v (σ i)} ∧
      (ggAutomizer K Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
          T v i = ((if i.val = 0 then (-1 : ZMod 3) else 1) *
            (if (σ i).val = 0 then (-1 : ZMod 3) else 1)) * v (σ i)} ∧
      ι (Additive.ofMul ⟨x, hx⟩) = (fun _ => 1) ∧
      ι (Additive.ofMul ⟨y, hy⟩) = (fun i => if i.val = 0 then (-1 : ZMod 3) else 1)

theorem ggQTwoXInLNbrClassical_of_frames
    (hU : GGQTwoXInLFrameUnitary) (hF : GGQTwoXInLFrameFormed)
    (hA : ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
        GGQTwoSetting 3 B Bs x L D J → GGQTwoI1 Bs D J → x ∈ L → GGQTwoXInLAmbOn (fun t => t = .A)
        Bs (ggG0 3 B x L D J) → False) : GGQTwoXInLNbrClassical := by
  intro G _ _ p B Bs x L D J hS hI hxL hAmb hp
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  have hcl : ∀ t, GGQTwoXInLClTag t → (t = .A) ∨ (t = .twA) ∨
      (t = .B ∨ t = .C ∨ t = .D ∨ t = .twD) := by
    intro t ht
    rcases ht with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  rcases ggQTwoXInL_ambOn_cases hcl hAmb with hAmb | hAmb | hAmb
  · exact (hA G B Bs x L D J hS hI hxL hAmb).elim
  · obtain ⟨n, hn3, hn6, y, K, hx, hy, ι, hnb, hL, hK, hxv, hyv⟩ := hU G B Bs x L D J hS hI hxL hAmb
    exact ⟨y, K, hnb, ggQTwoXInL_model_unitary n hn3 hn6 hx hy ι hL hK hxv hyv⟩
  · obtain ⟨n, hn6, y, K, hx, hy, ι, hnb, hL, hK, hxv, hyv⟩ := hF G B Bs x L D J hS hI hxL hAmb
    exact ⟨y, K, hnb, ggQTwoXInL_model_formed n hn6 hx hy ι hL hK hxv hyv⟩

end CFSG.StandardType

end
