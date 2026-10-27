module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.ProdDefs
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.ProdNormal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Kernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open Subgroup

variable {G S₀ : Type*} [Group G] [Group S₀] {H : Subgroup G}

private def conjSubtype {s : G} (hs : s ∈ normalizer (H : Set G)) : ↥H ≃* ↥H where
  toFun x := ⟨s * x * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs x).mp x.2⟩
  invFun x := ⟨s⁻¹ * x * s,
    by simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hs) x).mp x.2⟩
  left_inv x := by ext; group
  right_inv x := by ext; group
  map_mul' x y := by ext; simp

private lemma map_center_conj_eq {s : G} (hs : s ∈ normalizer (H : Set G)) :
    (Subgroup.center ↥H).map (conjSubtype hs).toMonoidHom = Subgroup.center ↥H :=
  Subgroup.map_center_eq (conjSubtype hs)

private lemma map_center_subtype_conj_eq {s : G} (hs : s ∈ normalizer (H : Set G)) :
    (((Subgroup.center ↥H).map H.subtype).map (MulAut.conj s).toMonoidHom =
      (Subgroup.center ↥H).map H.subtype) := by
  have hcomp : (MulAut.conj s).toMonoidHom.comp H.subtype =
      H.subtype.comp (conjSubtype hs).toMonoidHom := by
    ext x
    rfl
  calc
    ((Subgroup.center ↥H).map H.subtype).map (MulAut.conj s).toMonoidHom
        = (Subgroup.center ↥H).map ((MulAut.conj s).toMonoidHom.comp H.subtype) := by
          rw [Subgroup.map_map]
    _ = (Subgroup.center ↥H).map (H.subtype.comp (conjSubtype hs).toMonoidHom) := by
          rw [hcomp]
    _ = ((Subgroup.center ↥H).map (conjSubtype hs).toMonoidHom).map H.subtype := by
          rw [Subgroup.map_map]
    _ = (Subgroup.center ↥H).map H.subtype := by rw [map_center_conj_eq hs]

private lemma ker_eq_center [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    (g : ↥H →* S₀ × S₀) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥H) : g.ker = Subgroup.center ↥H := by
  refine le_antisymm hker ?_
  have hScent : Subgroup.center S₀ = ⊥ := center_eq_bot_of_isSimpleGroup hS
  have hprod : Subgroup.center (S₀ × S₀) = ⊥ := by
    rw [Subgroup.center_prod, hScent, Subgroup.bot_prod_bot]
  intro z hz
  rw [MonoidHom.mem_ker]
  have hzprod : g z ∈ Subgroup.center (S₀ × S₀) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := hg y
    have hcomm := Subgroup.mem_center_iff.mp hz w
    rw [← map_mul, ← map_mul, hcomm]
  simpa [hprod] using hzprod

private lemma ker_comap_snd (g : ↥H →* S₀ × S₀) :
    (MonoidHom.snd S₀ S₀).ker.comap g = ((MonoidHom.snd S₀ S₀).comp g).ker := by
  rw [← MonoidHom.comap_bot (f := MonoidHom.snd S₀ S₀), Subgroup.comap_comap,
    MonoidHom.comap_bot]

private lemma ker_comap_fst (g : ↥H →* S₀ × S₀) :
    (MonoidHom.fst S₀ S₀).ker.comap g = ((MonoidHom.fst S₀ S₀).comp g).ker := by
  rw [← MonoidHom.comap_bot (f := MonoidHom.fst S₀ S₀), Subgroup.comap_comap,
    MonoidHom.comap_bot]

private lemma subgroupOf_prodFst (g : ↥H →* S₀ × S₀) :
    (prodFst g).subgroupOf H = ((MonoidHom.snd S₀ S₀).comp g).ker := by
  change ((((MonoidHom.snd S₀ S₀).comp g).ker.map H.subtype).subgroupOf H) =
    ((MonoidHom.snd S₀ S₀).comp g).ker
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)]

private lemma subgroupOf_prodSnd (g : ↥H →* S₀ × S₀) :
    (prodSnd g).subgroupOf H = ((MonoidHom.fst S₀ S₀).comp g).ker := by
  change ((((MonoidHom.fst S₀ S₀).comp g).ker.map H.subtype).subgroupOf H) =
    ((MonoidHom.fst S₀ S₀).comp g).ker
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)]

private lemma map_subgroupOf_prodFst (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) :
    ((prodFst g).subgroupOf H).map g = (MonoidHom.snd S₀ S₀).ker := by
  rw [subgroupOf_prodFst, ← ker_comap_snd]
  exact Subgroup.map_comap_eq_self_of_surjective hg _

private lemma map_subgroupOf_prodSnd (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) :
    ((prodSnd g).subgroupOf H).map g = (MonoidHom.fst S₀ S₀).ker := by
  rw [subgroupOf_prodSnd, ← ker_comap_fst]
  exact Subgroup.map_comap_eq_self_of_surjective hg _

private lemma prodFst_ne_prodSnd (hS : ∃ a b : S₀, a * b ≠ b * a)
    (g : ↥H →* S₀ × S₀) (hg : Function.Surjective g) : prodFst g ≠ prodSnd g := by
  intro h
  have hmap : (MonoidHom.snd S₀ S₀).ker = (MonoidHom.fst S₀ S₀).ker := by
    rw [← map_subgroupOf_prodFst g hg, ← map_subgroupOf_prodSnd g hg, h]
  have ha_exists : ∃ a : S₀, a ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hS
    exact ⟨a, fun ha => hab (by rw [ha, one_mul, mul_one])⟩
  obtain ⟨a, ha⟩ := ha_exists
  have hmem : (1, a) ∈ (MonoidHom.fst S₀ S₀).ker := by
    rw [MonoidHom.mem_ker]
    rfl
  have hnot : (1, a) ∉ (MonoidHom.snd S₀ S₀).ker := by
    rw [MonoidHom.mem_ker]
    simpa using ha
  apply hnot
  rw [hmap]
  exact hmem

private lemma subgroupOf_map_conj_eq {s : G} (hs : s ∈ normalizer (H : Set G))
    (K : Subgroup G) (hKle : K ≤ H) :
    (K.map (MulAut.conj s).toMonoidHom).subgroupOf H =
      (K.subgroupOf H).map (conjSubtype hs).toMonoidHom := by
  have hK'le : K.map (MulAut.conj s).toMonoidHom ≤ H := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hs]
    exact Subgroup.map_mono hKle
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_subgroupOf_eq_of_le hK'le]
  calc
    K.map (MulAut.conj s).toMonoidHom
        = ((K.subgroupOf H).map H.subtype).map (MulAut.conj s).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hKle]
    _ = (K.subgroupOf H).map ((MulAut.conj s).toMonoidHom.comp H.subtype) := by
          rw [Subgroup.map_map]
    _ = (K.subgroupOf H).map (H.subtype.comp (conjSubtype hs).toMonoidHom) := by
          rw [show (MulAut.conj s).toMonoidHom.comp H.subtype =
            H.subtype.comp (conjSubtype hs).toMonoidHom from by ext x; rfl]
    _ = ((K.subgroupOf H).map (conjSubtype hs).toMonoidHom).map H.subtype := by
          rw [Subgroup.map_map]

private lemma map_conj_eq_prod_of_comap [IsSimpleGroup S₀]
    (hS : ∃ a b : S₀, a * b ≠ b * a) (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) (hker : g.ker ≤ Subgroup.center ↥H) {s : G}
    (hs : s ∈ normalizer (H : Set G)) (K : Subgroup G) (hKle : K ≤ H)
    (N₀ : Subgroup (S₀ × S₀)) (hN₀ : N₀.Normal)
    (hKH : K.subgroupOf H = N₀.comap g) (hN₀bot : N₀ ≠ ⊥) (hN₀top : N₀ ≠ ⊤) :
    K.map (MulAut.conj s).toMonoidHom = prodFst g ∨
      K.map (MulAut.conj s).toMonoidHom = prodSnd g := by
  classical
  let K' : Subgroup G := K.map (MulAut.conj s).toMonoidHom
  have hK'le : K' ≤ H := by
    rw [show K' = K.map (MulAut.conj s).toMonoidHom from rfl]
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hs]
    exact Subgroup.map_mono hKle
  have hK'H_eq : K'.subgroupOf H =
      (K.subgroupOf H).map (conjSubtype hs).toMonoidHom :=
    subgroupOf_map_conj_eq hs K hKle
  have hKH_normal : (K.subgroupOf H).Normal := by
    rw [hKH]
    exact hN₀.comap g
  have hK'H_normal : (K'.subgroupOf H).Normal := by
    rw [hK'H_eq]
    exact Subgroup.Normal.map hKH_normal (conjSubtype hs).toMonoidHom
      (conjSubtype hs).surjective
  let N : Subgroup (S₀ × S₀) := (K'.subgroupOf H).map g
  have hN : N.Normal := Subgroup.Normal.map hK'H_normal g hg
  have hZeq : ((Subgroup.center ↥H).map H.subtype : Subgroup G) =
      (g.ker).map H.subtype := by rw [ker_eq_center hS g hg hker]
  have hZ_conj : ((Subgroup.center ↥H).map H.subtype : Subgroup G).map
      (MulAut.conj s).toMonoidHom = (Subgroup.center ↥H).map H.subtype :=
    map_center_subtype_conj_eq hs
  have hZK : ((Subgroup.center ↥H).map H.subtype : Subgroup G) ≤ K := by
    rw [hZeq]
    rintro x ⟨y, hy, rfl⟩
    refine Subgroup.mem_subgroupOf.mp ?_
    rw [hKH]
    exact Subgroup.mem_comap.mpr (by
      rw [MonoidHom.mem_ker.mp hy]
      exact N₀.one_mem)
  have hZK' : ((Subgroup.center ↥H).map H.subtype : Subgroup G) ≤ K' := by
    calc
      ((Subgroup.center ↥H).map H.subtype : Subgroup G)
          = ((Subgroup.center ↥H).map H.subtype : Subgroup G).map
              (MulAut.conj s).toMonoidHom := hZ_conj.symm
      _ ≤ K.map (MulAut.conj s).toMonoidHom := Subgroup.map_mono hZK
  have hker_le_K'H : g.ker ≤ K'.subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hZK' (by
      rw [hZeq]
      exact Subgroup.mem_map_of_mem H.subtype hx)
  have hcomap : K'.subgroupOf H = N.comap g :=
    (Subgroup.comap_map_eq_self (f := g) hker_le_K'H).symm
  have hmap_KH : (K.subgroupOf H).map g = N₀ := by
    rw [hKH]
    exact Subgroup.map_comap_eq_self_of_surjective hg N₀
  rcases normal_prod_cases hS hN with hNbot | hNsnd | hNfst | hNtop
  · exfalso
    have hK'H_bot : K'.subgroupOf H = g.ker := by
      rw [hcomap, hNbot, MonoidHom.comap_bot]
    have hK'Z : K' = (Subgroup.center ↥H).map H.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hK'le, hK'H_bot, hZeq]
    have hKZ : K = (Subgroup.center ↥H).map H.subtype := by
      apply Subgroup.map_injective (f := (MulAut.conj s).toMonoidHom)
      exact (MulAut.conj s).injective
      rw [show K.map (MulAut.conj s).toMonoidHom = K' from rfl, hK'Z, hZ_conj]
    have hN₀_eq_bot : N₀ = ⊥ := by
      rw [← hmap_KH, hKZ]
      rw [show ((Subgroup.center ↥H).map H.subtype).subgroupOf H = K'.subgroupOf H by
        rw [hK'Z]]
      exact hNbot
    exact hN₀bot hN₀_eq_bot
  · left
    have hK'H_snd : K'.subgroupOf H = (prodFst g).subgroupOf H := by
      rw [hcomap, hNsnd, ker_comap_snd, subgroupOf_prodFst]
    calc
      K.map (MulAut.conj s).toMonoidHom = K' := rfl
      _ = (K'.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hK'le).symm
      _ = ((prodFst g).subgroupOf H).map H.subtype := by rw [hK'H_snd]
      _ = prodFst g := Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)
  · right
    have hK'H_fst : K'.subgroupOf H = (prodSnd g).subgroupOf H := by
      rw [hcomap, hNfst, ker_comap_fst, subgroupOf_prodSnd]
    calc
      K.map (MulAut.conj s).toMonoidHom = K' := rfl
      _ = (K'.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hK'le).symm
      _ = ((prodSnd g).subgroupOf H).map H.subtype := by rw [hK'H_fst]
      _ = prodSnd g := Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)
  · exfalso
    have hK'H_top : K'.subgroupOf H = ⊤ := by
      rw [hcomap, hNtop, Subgroup.comap_top]
    have htopmap : ((⊤ : Subgroup ↥H).map H.subtype : Subgroup G) = H := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have hK'H : K' = H := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hK'le, hK'H_top, htopmap]
    have hKH_eq : K = H := by
      apply Subgroup.map_injective (f := (MulAut.conj s).toMonoidHom)
      exact (MulAut.conj s).injective
      rw [show K.map (MulAut.conj s).toMonoidHom = K' from rfl, hK'H]
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hs).symm
    have hN₀_eq_top : N₀ = ⊤ := by
      rw [← hmap_KH, hKH_eq, Subgroup.subgroupOf_self,
        Subgroup.map_top_of_surjective g hg]
    exact hN₀top hN₀_eq_top

theorem conj_prod_cases [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a) (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) (hker : g.ker ≤ center ↥H) {s : G}
    (hs : s ∈ normalizer (H : Set G)) :
    ((prodFst g).map (MulAut.conj s).toMonoidHom = prodFst g ∧
        (prodSnd g).map (MulAut.conj s).toMonoidHom = prodSnd g) ∨
      ((prodFst g).map (MulAut.conj s).toMonoidHom = prodSnd g ∧
        (prodSnd g).map (MulAut.conj s).toMonoidHom = prodFst g) := by
  have ha_exists : ∃ a : S₀, a ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hS
    exact ⟨a, fun ha => hab (by rw [ha, one_mul, mul_one])⟩
  obtain ⟨a, ha⟩ := ha_exists
  have hker_snd_ne_bot : (MonoidHom.snd S₀ S₀).ker ≠ ⊥ := by
    intro h
    have hmem : (a, 1) ∈ (MonoidHom.snd S₀ S₀).ker := by
      rw [MonoidHom.mem_ker]
      rfl
    rw [h] at hmem
    exact ha (congrArg Prod.fst (Subgroup.mem_bot.mp hmem))
  have hker_snd_ne_top : (MonoidHom.snd S₀ S₀).ker ≠ ⊤ := by
    intro h
    have hmem : (1, a) ∈ (MonoidHom.snd S₀ S₀).ker := by
      rw [h]
      trivial
    rw [MonoidHom.mem_ker] at hmem
    exact ha hmem
  have hker_fst_ne_bot : (MonoidHom.fst S₀ S₀).ker ≠ ⊥ := by
    intro h
    have hmem : (1, a) ∈ (MonoidHom.fst S₀ S₀).ker := by
      rw [MonoidHom.mem_ker]
      rfl
    rw [h] at hmem
    exact ha (congrArg Prod.snd (Subgroup.mem_bot.mp hmem))
  have hker_fst_ne_top : (MonoidHom.fst S₀ S₀).ker ≠ ⊤ := by
    intro h
    have hmem : (a, 1) ∈ (MonoidHom.fst S₀ S₀).ker := by
      rw [h]
      trivial
    rw [MonoidHom.mem_ker] at hmem
    exact ha hmem
  have hK1 := map_conj_eq_prod_of_comap hS g hg hker hs (prodFst g)
    (Subgroup.map_subtype_le _) ((MonoidHom.snd S₀ S₀).ker) inferInstance
    (by rw [subgroupOf_prodFst, ← ker_comap_snd]) hker_snd_ne_bot hker_snd_ne_top
  have hK2 := map_conj_eq_prod_of_comap hS g hg hker hs (prodSnd g)
    (Subgroup.map_subtype_le _) ((MonoidHom.fst S₀ S₀).ker) inferInstance
    (by rw [subgroupOf_prodSnd, ← ker_comap_fst]) hker_fst_ne_bot hker_fst_ne_top
  have hne : prodFst g ≠ prodSnd g := prodFst_ne_prodSnd hS g hg
  rcases hK1 with h1 | h1 <;> rcases hK2 with h2 | h2
  · exfalso
    have h_eq : prodFst g = prodSnd g := by
      apply Subgroup.map_injective (f := (MulAut.conj s).toMonoidHom)
      exact (MulAut.conj s).injective
      rw [h1, h2]
    exact hne h_eq
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exfalso
    have h_eq : prodFst g = prodSnd g := by
      apply Subgroup.map_injective (f := (MulAut.conj s).toMonoidHom)
      exact (MulAut.conj s).injective
      rw [h1, h2]
    exact hne h_eq

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
