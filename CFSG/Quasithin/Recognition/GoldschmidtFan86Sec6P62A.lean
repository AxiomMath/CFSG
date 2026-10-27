module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PTrans
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Swap

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

theorem exists_smul_of_valence_eq (F : FanTree Γ G) {u w : V} (h : valence Γ w = valence Γ u) :
    ∃ g : G, g • u = w := by
  obtain ⟨p⟩ := F.isTree.connected.preconnected u w
  obtain ⟨n, hn⟩ := (F.walk_even_iff p).1 h
  exact F.exists_smul_of_walk_even n p (by omega)

@[expose] def NoncommAt (L : ZLab Γ G) (d : V) : Prop :=
  ∃ l m, Γ.dist d l = 2 ∧ Γ.dist d m = 2 ∧ NC L l m

variable {L : ZLab Γ G} (F : FanTree Γ G)
include F

theorem NoncommAt.smul {d : V} (hd : valence Γ d = 5) (h : NoncommAt L d) (g : G) :
    NoncommAt L (g • d) := by
  obtain ⟨l, m, hl, hm, hnc⟩ := h
  obtain ⟨ν, hν⟩ := exists_br F hl
  obtain ⟨μ, hμ⟩ := exists_br F hm
  exact ⟨g • l, g • m, Br.dist_two F (Br.smul F g hν), Br.dist_two F (Br.smul F g hμ),
    (NC.smul (Br.valence F hd hν).2 (Br.valence F hd hμ).2 g).2 hnc⟩

theorem noncomm_all {d₀ d : V} (hd₀ : valence Γ d₀ = 5) (hd : valence Γ d = 5)
    (h : NoncommAt L d₀) : NoncommAt L d := by
  obtain ⟨g, hg⟩ := exists_smul_of_valence_eq F (u := d₀) (w := d) (by rw [hd, hd₀])
  rw [← hg]
  exact NoncommAt.smul F hd₀ h g

theorem exists_nc_partner (h40 : Fan40 F) {d l₀ : V} (hd : valence Γ d = 5)
    (hN : NoncommAt L d) (hl₀ : Γ.dist d l₀ = 2) : ∃ m, Γ.dist d m = 2 ∧ NC L l₀ m := by
  obtain ⟨l₁, m₁, hl₁, hm₁, hnc⟩ := hN
  obtain ⟨ν₁, hν₁⟩ := exists_br F hl₁
  obtain ⟨μ₁, hμ₁⟩ := exists_br F hm₁
  obtain ⟨ν₀, hν₀⟩ := exists_br F hl₀
  obtain ⟨g, hg, hgl⟩ := exists_stab_smul_br F h40 hd hν₁ hν₀
  have hgd : g • d = d := MulAction.mem_stabilizer_iff.1 hg
  have hbr := Br.smul F g hμ₁
  rw [hgd] at hbr
  refine ⟨g • m₁, Br.dist_two F hbr, ?_⟩
  have := (NC.smul (L := L) (Br.valence F hd hν₁).2 (Br.valence F hd hμ₁).2 g).2 hnc
  rwa [hgl] at this

theorem lemma_A (h40 : Fan40 F) (H : LabHyp L) {d l₀ : V} {y : G} (hd : valence Γ d = 5)
    (hN : NoncommAt L d) (hl₀ : Γ.dist d l₀ = 2) (hy : y ∈ MulAction.stabilizer G d)
    (hy2 : y * y = L.z l₀) : y ∉ nbrStab Γ G d := by
  intro hyK
  obtain ⟨m, hm, hnc⟩ := exists_nc_partner F h40 hd hN hl₀
  apply hnc
  obtain ⟨c, hc⟩ := exists_br F hm
  have hvm := (Br.valence F hd hc).2
  obtain ⟨m', hm', hne, -⟩ := exists_sibling F hd hc
  have hyd : y * L.z d * y⁻¹ = L.z d := by
    rw [z_comm hd hy]
    group
  have hsw := nbrStab_swap F hd hyK hc hm' hne.symm
  have hz := z_smul (L := L) hvm y
  have hcomm : y * y * L.z m * (y * y)⁻¹ = L.z m := by
    rcases hsw with h1 | h1
    · rw [h1] at hz
      calc y * y * L.z m * (y * y)⁻¹ = y * (y * L.z m * y⁻¹) * y⁻¹ := by group
        _ = L.z m := by rw [← hz]; exact hz.symm
    · rw [h1, sib_label F H hd hc hm' hne.symm] at hz
      calc y * y * L.z m * (y * y)⁻¹ = y * (y * L.z m * y⁻¹) * y⁻¹ := by group
        _ = y * (L.z m * L.z d) * y⁻¹ := by rw [← hz]
        _ = (y * L.z m * y⁻¹) * (y * L.z d * y⁻¹) := by group
        _ = (L.z m * L.z d) * L.z d := by rw [← hz, hyd]
        _ = L.z m := by rw [mul_assoc, z_sq hd, mul_one]
  rw [← hy2]
  exact mul_inv_eq_iff_eq_mul.1 hcomm

end P62

end CFSG.Quasithin.Fan86
