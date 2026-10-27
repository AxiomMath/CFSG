module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34BL3Fin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34BL12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

namespace BL3

variable {G : Type} [Group G] {D Q X : Subgroup G}

def img (θ : ↥D →* Perm (Fin 5)) (X : Subgroup G) : Subgroup (Perm (Fin 5)) :=
  (X.subgroupOf D).map θ

def preimg (θ : ↥D →* Perm (Fin 5)) (K : Subgroup (Perm (Fin 5))) : Subgroup G :=
  (K.comap θ).map D.subtype

theorem mem_img {θ : ↥D →* Perm (Fin 5)} {τ : Perm (Fin 5)} :
    τ ∈ img θ X ↔ ∃ x : ↥D, (x : G) ∈ X ∧ θ x = τ := by
  simp [img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mem_preimg {θ : ↥D →* Perm (Fin 5)} {K : Subgroup (Perm (Fin 5))} {x : G} :
    x ∈ preimg θ K ↔ ∃ h : x ∈ D, θ ⟨x, h⟩ ∈ K := by
  simp [preimg, Subgroup.mem_map]

theorem mem_of_mem_img {θ : ↥D →* Perm (Fin 5)} (hQX : Q ≤ X)
    (hker : ∀ x : ↥D, θ x = 1 ↔ (x : G) ∈ Q) {z : ↥D} (hz : θ z ∈ img θ X) : (z : G) ∈ X := by
  obtain ⟨x, hxX, hx⟩ := mem_img.mp hz
  have h1 : (↑(z * x⁻¹) : G) ∈ X := by
    refine hQX ((hker _).mp ?_)
    rw [map_mul, map_inv, hx, mul_inv_cancel]
  have := X.mul_mem h1 hxX
  simpa using this

theorem le_of_img_eq_top {θ : ↥D →* Perm (Fin 5)} (hQX : Q ≤ X)
    (hker : ∀ x : ↥D, θ x = 1 ↔ (x : G) ∈ Q) (h : img θ X = ⊤) : D ≤ X := fun d hd =>
  mem_of_mem_img hQX hker (z := ⟨d, hd⟩) (h ▸ Subgroup.mem_top _)

theorem inv_mul_mem_of_relIndex_two {B Q : Subgroup G} (h : (B ⊓ Q).relIndex B = 2) {y b : G}
    (hy : y ∈ B) (hyQ : y ∉ Q) (hb : b ∈ B) (hbQ : b ∉ Q) : y⁻¹ * b ∈ Q := by
  have h2 : ((B ⊓ Q).subgroupOf B).index = 2 := h
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨y⁻¹, B.inv_mem hy⟩) (b := ⟨b, hb⟩)).mpr
    (by
      have e1 : (⟨y⁻¹, B.inv_mem hy⟩ : ↥B) ∉ (B ⊓ Q).subgroupOf B := fun h' =>
        hyQ (by simpa using (Subgroup.mem_subgroupOf.mp h').2)
      have e2 : (⟨b, hb⟩ : ↥B) ∉ (B ⊓ Q).subgroupOf B := fun h' =>
        hbQ (Subgroup.mem_subgroupOf.mp h').2
      exact iff_of_false e1 e2)
  exact (Subgroup.mem_subgroupOf.mp this).2

end BL3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

theorem block_transitive (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ')
    {α : Geo H M} (hα : α ∈ nbrs δ) (hbad : ¬ Zv α ≤ Qv δ') :
    stab δ ≤ (stab δ ⊓ stab α) ⊔ Vn δ' ⊔ Qv δ := by
  have hδ := hp.vδ
  obtain ⟨n, θ, hn, hθs, hker⟩ := exists_quotHom hG.amalg δ
  obtain rfl : n = 5 := by
    rcases hn with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · rw [hδ] at h
      exact absurd h (by decide)
  by_contra hX
  have hQD : Qv δ ≤ stab δ := pCoreOf_le 2 _
  have hBD : Vn δ' ≤ stab δ := (pd_Vn_le_stab hG hp).2
  have hQX : Qv δ ≤ (stab δ ⊓ stab α) ⊔ Vn δ' ⊔ Qv δ := le_sup_right
  have hPα : Nat.card (BL3.img θ (stab δ ⊓ stab α)) = 8 :=
    card_image_sylow hθs (sylow_stab_inf_left hG.amalg hα)
  obtain ⟨r, hrfix, hrtr⟩ := exists_fix_trans_of_card_eight _ hPα
  have hPK : BL3.img θ (stab δ ⊓ stab α) ≤ BL3.img θ ((stab δ ⊓ stab α) ⊔ Vn δ' ⊔ Qv δ) := by
    intro τ hτ
    obtain ⟨x, hx, rfl⟩ := BL3.mem_img.mp hτ
    have hle : stab δ ⊓ stab α ≤ (stab δ ⊓ stab α) ⊔ Vn δ' ⊔ Qv δ :=
      le_sup_left.trans le_sup_left
    exact BL3.mem_img.mpr ⟨x, hle hx, rfl⟩
  have hKT : BL3.img θ ((stab δ ⊓ stab α) ⊔ Vn δ' ⊔ Qv δ) ≤
      MulAction.stabilizer (Perm (Fin 5)) r := by
    by_contra hK
    exact hX (BL3.le_of_img_eq_top hQX hker (F5b_core _ _ hPα r hrtr hPK hK))
  have hidx := (c3_idx_two hG hirr h15 hng hp).2
  obtain ⟨y, hyB, hy'⟩ : ∃ y ∈ Vn δ', y ∉ Vn δ' ⊓ Qv δ := by
    by_contra h
    push Not at h
    have := Subgroup.relIndex_eq_one.mpr fun y hy => h y hy
    omega
  have hyQ : y ∉ Qv δ := fun h => hy' ⟨hyB, h⟩
  have hyD : y ∈ stab δ := hBD hyB
  have hy2 : y * y = 1 := by
    have := (isElemAbelian_Vn' hG δ').2 y hyB
    simpa [pow_two] using this
  have ht2 : θ ⟨y, hyD⟩ * θ ⟨y, hyD⟩ = 1 := by
    rw [← map_mul, ← map_one θ]
    exact congrArg θ (Subtype.ext hy2)
  have hBX : Vn δ' ≤ (stab δ ⊓ stab α) ⊔ Vn δ' ⊔ Qv δ := le_sup_right.trans le_sup_left
  have hyX : y ∈ (stab δ ⊓ stab α) ⊔ Vn δ' ⊔ Qv δ := hBX hyB
  have htr : θ ⟨y, hyD⟩ r = r := by
    have := hKT (BL3.mem_img.mpr ⟨⟨y, hyD⟩, hyX, rfl⟩)
    simpa [MulAction.mem_stabilizer_iff] using this
  obtain ⟨P, hP8, htP, hPfix⟩ := BL3.exists_card_eight_of_fix _ ht2 r htr
  obtain ⟨σ, hσ⟩ := BL3.exists_conj_of_card_eight _ P hPα hP8
  obtain ⟨gd, hgd⟩ := hθs σ
  let g : ↥(H ⊔ M) := ⟨(gd : G), stab_le δ gd.2⟩
  have hgδ : g • δ = δ := smul_eq_of_mem_stab gd.2
  have hν : g • α ∈ nbrs δ := by
    have := (smul_adj g).mpr (show (graph (H ⊔ M) H M).Adj δ α from hα)
    rw [hgδ] at this
    exact this
  have hstabν : ∀ x : G, x ∈ stab (g • α) ↔ (gd : G)⁻¹ * x * gd ∈ stab α := by
    intro x
    rw [stab_smul]
    exact mem_conjSub
  have hQα : Qv δ ≤ stab δ ⊓ stab α := le_inf hQD (Qv_le_stab_of_mem_nbrs hG.amalg hα)
  have key : ∀ x : ↥(stab δ), (x : G) ∈ stab (g • α) ↔ θ x ∈ P := by
    intro x
    have hz : θ (gd⁻¹ * x * gd) = σ⁻¹ * θ x * σ := by simp [map_mul, hgd]
    have hzG : ((gd⁻¹ * x * gd : ↥(stab δ)) : G) = (gd : G)⁻¹ * x * gd := rfl
    rw [hstabν, ← hzG, hσ, ← hz]
    constructor
    · intro h
      exact BL3.mem_img.mpr ⟨gd⁻¹ * x * gd, ⟨(gd⁻¹ * x * gd).2, h⟩, rfl⟩
    · intro h
      exact (BL3.mem_of_mem_img hQα hker h).2
  have hyν : y ∈ stab (g • α) := (key ⟨y, hyD⟩).mpr htP
  have hQν : Qv δ ≤ stab (g • α) := Qv_le_stab_of_mem_nbrs hG.amalg hν
  have hBν : Vn δ' ≤ stab (g • α) := by
    intro b hb
    by_cases hbQ : b ∈ Qv δ
    · exact hQν hbQ
    · have h1 := BL3.inv_mul_mem_of_relIndex_two hidx hyB hyQ hb hbQ
      have h2 : b = y * (y⁻¹ * b) := by group
      rw [h2]
      exact (stab (g • α)).mul_mem hyν (hQν h1)
  have hsb : SameBlock δ α (g • α) := by
    refine ⟨BL3.preimg θ (MulAction.stabilizer (Perm (Fin 5)) r), ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      refine BL3.mem_preimg.mpr ⟨hQD hq, ?_⟩
      rw [(hker ⟨q, hQD hq⟩).mpr hq]
      exact one_mem _
    · exact fun x hx => (BL3.mem_preimg.mp hx).1
    · intro h
      obtain ⟨d, hd⟩ := hθs (Equiv.swap r (r + 1))
      have hmem : (d : G) ∈ BL3.preimg θ (MulAction.stabilizer (Perm (Fin 5)) r) := by
        rw [h]
        exact d.2
      obtain ⟨hdD, h3⟩ := BL3.mem_preimg.mp hmem
      have h4 : θ d r = r := by simpa [MulAction.mem_stabilizer_iff] using h3
      rw [hd, Equiv.swap_apply_left] at h4
      exact (show ∀ r : Fin 5, r + 1 ≠ r by decide) r h4
    · intro x hx
      refine BL3.mem_preimg.mpr ⟨hx.1, ?_⟩
      have := hrfix _ (BL3.mem_img.mpr ⟨⟨x, hx.1⟩, hx, rfl⟩)
      simpa [MulAction.mem_stabilizer_iff] using this
    · intro x hx
      refine BL3.mem_preimg.mpr ⟨hx.1, ?_⟩
      have := hPfix _ ((key ⟨x, hx.1⟩).mp hx.2)
      simpa [MulAction.mem_stabilizer_iff] using this
  exact bad_not_fixed hG hirr h15 hng hp hν (bad_block hG hirr h15 hng hp hα hν hsb hbad) hBν

end S34

end F53.Stellmacher

end CFSG.Quasithin
