module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123CentralZeroAbs
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

section A7Cohomology



theorem a7Four_fixV_eq_bot' {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {V : Subgroup W} (hinv : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V)
    (hcomm : commSub V L = V) (h : A7Four L V (V ⊓ fixV L)) : V ⊓ fixV L = ⊥ := by
  obtain ⟨α, π₀, hπs₀, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  let π : ↥(alternatingGroup (Fin 7)) →* ↥L := π₀
  have hπs : Function.Surjective π := hπs₀
  have hLs : L ≤ stabSub V := by
    intro g hg u
    refine ⟨fun hu => ?_, hinv g hg u⟩
    have h1 := hinv g⁻¹ (L.inv_mem hg) (g u) hu
    rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h1
  let act : ↥(alternatingGroup (Fin 7)) →* MulAut ↥V :=
    (resHom V).comp ((Subgroup.inclusion hLs).comp π)
  have hact : ∀ (g : ↥(alternatingGroup (Fin 7))) (v : ↥V),
      ((act g v : ↥V) : W) = ((π g : ↥L) : MulAut W) (v : W) := fun g v => rfl
  have hZfix : ∀ (g : ↥(alternatingGroup (Fin 7))), ∀ z ∈ (V ⊓ fixV L).subgroupOf V,
      act g z = z := by
    intro g z hz
    apply Subtype.ext
    rw [hact]
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).2 _ (π g).2
  have hker : β.ker = (V ⊓ fixV L).subgroupOf V := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have hQ : Nat.card (↥(FFModel.a7Four α).sec ⧸
      (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec) = 2 ^ 4 := by
    show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))).subgroupOf ⊤) = 2 ^ 4
    rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_fin]
  have hcard : Nat.card ↥V = 16 * Nat.card ↥((V ⊓ fixV L).subgroupOf V) := by
    have h1 := Subgroup.card_ker_mul_card_range β
    rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top, hker, hQ] at h1
    have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
    rw [h16] at h1
    omega
  have hgen : Subgroup.closure {x : ↥V | ∃ (g : ↥(alternatingGroup (Fin 7))) (v : ↥V),
      x = act g v * v⁻¹} = ⊤ := by
    set S : Subgroup ↥V := Subgroup.closure {x : ↥V | ∃ (g : ↥(alternatingGroup (Fin 7)))
      (v : ↥V), x = act g v * v⁻¹} with hS
    have hle : commSub V L ≤ S.map V.subtype := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      obtain ⟨g, hg⟩ := hπs ⟨x, hx⟩
      refine ⟨act g ⟨w, hw⟩ * (⟨w, hw⟩ : ↥V)⁻¹,
        Subgroup.subset_closure ⟨g, ⟨w, hw⟩, rfl⟩, ?_⟩
      show ((act g ⟨w, hw⟩ : ↥V) : W) * w⁻¹ = x w * w⁻¹
      rw [hact, hg]
    rw [eq_top_iff]
    intro u _
    have hu : (u : W) ∈ commSub V L := by rw [hcomm]; exact u.2
    obtain ⟨s, hs, hsu⟩ := hle hu
    have hsu' : s = u := Subtype.ext hsu
    rwa [hsu'] at hs
  have hZ := CFSG.QuasithinUnique.L246.C123.central_zero_abstract (V := ↥V)
    (fun v => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hW2 (v : W)))
    act (MonoidHom.id _) Function.surjective_id
    (fun q hq => by rw [show q = 1 from hq, map_one]) ((V ⊓ fixV L).subgroupOf V) hZfix hcard hgen
  rw [eq_bot_iff]
  intro w hw
  have h1 : (⟨w, hw.1⟩ : ↥V) ∈ (V ⊓ fixV L).subgroupOf V := Subgroup.mem_subgroupOf.2 hw
  rw [hZ, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)

theorem a7Four_card_sixteen {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {V : Subgroup W} (hinv : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V)
    (hcomm : commSub V L = V) (h : A7Four L V (V ⊓ fixV L)) : Nat.card ↥V = 2 ^ 4 := by
  have hz := a7Four_fixV_eq_bot' hW2 hinv hcomm h
  obtain ⟨α, π₀, hπs₀, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hker : β.ker = (V ⊓ fixV L).subgroupOf V := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have hQ : Nat.card (↥(FFModel.a7Four α).sec ⧸
      (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec) = 2 ^ 4 := by
    show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))).subgroupOf ⊤) = 2 ^ 4
    rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_fin]
  have h1 := Subgroup.card_ker_mul_card_range β
  rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top, hker, hQ, hz, Subgroup.bot_subgroupOf,
    Subgroup.card_bot] at h1
  omega

end A7Cohomology

end CFSG.Quasithin.RonanF918
