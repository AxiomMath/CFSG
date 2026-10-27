module

public import CFSG.RankThree.GF2n.Smith81.S81YE4Def

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5

variable
  {K : Type} [Field K]

@[expose] noncomputable def xuLam [CharP K 2] {δ : Fin (Tag.rank .E7) → ℤ} (hδ : δ ∈ Perp) (b : K) :
    ↥(Lam K) :=
  ⟨e7Data_valid.xu K δ b, xu_mem_Lam hδ b⟩

theorem lamToG7_xuLam [CharP K 2] {δ : Fin (Tag.rank .E7) → ℤ} (hδ : δ ∈ Perp) (b : K) :
    lamToG7 (xuLam hδ b) = e7Data_valid.xm K δ b :=
  rfl

theorem act4_xuLam [CharP K 2] {δ : Fin (Tag.rank .E7) → ℤ} (hδ : δ ∈ Perp) (b : K) :
    act4 (xuLam hδ b) = vAut0 K (xuWUnit hδ b) := by
  have h : resV0 K (xuLam hδ b) = xuWUnit hδ b :=
    Induces.unique (resV0_induces _) (xuWUnit_induces hδ b)
  unfold act4
  rw [h]

theorem act4_conj_of_G7 [CharP K 2] {E l l' : ↥(Lam K)}
    (h : lamToG7 E * lamToG7 l * (lamToG7 E)⁻¹ = lamToG7 l') :
    act4 E * act4 l * (act4 E)⁻¹ = act4 l' := by
  have h' : E * l * E⁻¹ = l' := by
    apply Subtype.ext
    have h1 := congrArg Subtype.val h
    exact h1
  rw [← act4_inv, ← act4_mul, ← act4_mul, h']

theorem lamToG7_injective [CharP K 2] : Function.Injective (lamToG7 : ↥(Lam K) → G7 K) :=
  fun _ _ h => Subtype.ext (congrArg (fun g : G7 K => (g : (Module.End K (V K))ˣ)) h)

theorem lamToG7_mul [CharP K 2] (l l' : ↥(Lam K)) :
    lamToG7 (l * l') = lamToG7 l * lamToG7 l' :=
  rfl

theorem lamToG7_inv [CharP K 2] (l : ↥(Lam K)) : lamToG7 l⁻¹ = (lamToG7 l)⁻¹ :=
  rfl

theorem lamToG7_one [CharP K 2] : lamToG7 (1 : ↥(Lam K)) = 1 :=
  rfl

theorem exists_lam_of_mem_LG [CharP K 2] {g : G7 K} (hg : g ∈ LG K) :
    ∃ l : ↥(Lam K), lamToG7 l = g :=
  ⟨⟨(g : (Module.End K (V K))ˣ), mem_LG.1 hg⟩, rfl⟩

noncomputable def act4Hom [CharP K 2] : ↥(Lam K) →* (W K ≃ₗ[K] W K) where
  toFun := act4
  map_one' := act4_one
  map_mul' := act4_mul

theorem act4_pow [CharP K 2] (l : ↥(Lam K)) (n : ℕ) : act4 (l ^ n) = act4 l ^ n :=
  map_pow (act4Hom (K := K)) l n

theorem emb_xuWUnit [CharP K 2] {δ : Fin (Tag.rank .E7) → ℤ} (hδ : δ ∈ Perp) (b : K) (w : W K) :
    emb K (vAut0 K (xuWUnit hδ b) w) = act7 (e7Data_valid.xm K δ b) (emb K w) := by
  rw [← act4_xuLam, emb_act4, lamToG7_xuLam]

end CFSG.RankThree.GF2n.Smith81.RootGenE4
