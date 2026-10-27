module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem s16c11_v1_realizes_pull {W W' : Type} [CommGroup W] [CommGroup W'] {κ : W →* W'}
    (hκ : Function.Surjective κ) {A : Subgroup (MulAut W)} {B : Subgroup (MulAut W')}
    (e : ↥B →* ↥A) (he : Function.Surjective e)
    (hequiv : ∀ (b : ↥B) (w : W), κ ((e b : MulAut W) w) = (b : MulAut W') (κ w))
    (hker : ∀ w, κ w = 1 → w ∈ fixV A) {J : Subgroup W} {I : Subgroup W'}
    (hJ : J.map κ = I) (hfix : fixV B ⊓ I = ⊥) (hJA : ∀ a ∈ A, ∀ u ∈ J, a u ∈ J)
    {D : FFModel} (hR : D.Realizes B I ⊥) : D.Realizes A J (fixV A ⊓ J) := by
  obtain ⟨π, hπs, -, hkerle, hBI, hBZ, hsec, hkerinv, β', hβs, hβk, hβe⟩ := hR
  let q : ↥J →* ↥I :=
    ((κ.comp J.subtype).codRestrict I) fun u => by
      have hu : κ (u : W) ∈ J.map κ := Subgroup.mem_map.2 ⟨u, u.2, rfl⟩
      rwa [hJ] at hu
  have hq_coe : ∀ u : ↥J, ((q u : ↥I) : W') = κ (u : W) := fun u => rfl
  have hqs : Function.Surjective q := by
    intro i
    have hi : (i : W') ∈ J.map κ := by rw [hJ]; exact i.2
    obtain ⟨u, huJ, hu⟩ := Subgroup.mem_map.1 hi
    exact ⟨⟨u, huJ⟩, Subtype.ext hu⟩
  refine ⟨e.comp π, he.comp hπs, inf_le_right, hkerle, ?_, ?_, hsec, hkerinv, β'.comp q,
    hβs.comp hqs, ?_, ?_⟩
  · intro a u hu
    exact hJA a a.2 u hu
  · intro a z hz
    refine ⟨?_, hJA a a.2 z hz.2⟩
    intro a' ha'
    calc a' ((a : MulAut W) z) = (a' * a) z := (MulAut.mul_apply W a' a z).symm
      _ = z := hz.1 (a' * a) (A.mul_mem ha' a.2)
      _ = (a : MulAut W) z := (hz.1 a a.2).symm
  · intro u
    rw [MonoidHom.comp_apply, hβk, Subgroup.mem_bot]
    constructor
    · intro h1
      have hκ : κ (u : W) = 1 := by rw [← hq_coe u]; exact h1
      exact ⟨hker (u : W) hκ, u.2⟩
    · intro hu
      have huA : ∀ a ∈ A, a (u : W) = (u : W) := hu.1
      have hfixB : κ (u : W) ∈ fixV B := by
        intro b hb
        rw [← hequiv ⟨b, hb⟩ (u : W)]
        rw [huA (e ⟨b, hb⟩) (e ⟨b, hb⟩).2]
      have hmem : κ (u : W) ∈ fixV B ⊓ I := ⟨hfixB, (q u).2⟩
      rw [hfix] at hmem
      rw [hq_coe u]
      exact Subgroup.mem_bot.mp hmem
  · intro γ u m hu hm hbu
    have hqeq : q ⟨((e.comp π γ : ↥A) : MulAut W) (u : W), hu⟩ =
        ⟨((π γ : ↥B) : MulAut W') ((q u : ↥I) : W'), hBI (π γ) (q u) (q u).2⟩ :=
      Subtype.ext (by simpa [hq_coe] using hequiv (π γ) (u : W))
    rw [MonoidHom.comp_apply, hqeq]
    exact hβe γ (q u) m (hBI (π γ) (q u) (q u).2) hm hbu

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
