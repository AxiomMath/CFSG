module

public import CFSG.Quasithin.Background.SmithB45ExcEngine
public import Certificates.Certificate260380
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
  CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Blueprint


theorem m11O4Check_holds : m11O4Check = true :=
  Certificates.certificate260380

theorem m11_o4 {y : NativeSporadic.M11} (hy2 : y * y = 1)
    (hy1 : y ≠ 1) (hya : y * m11a = m11a * y) (hya' : y ≠ m11a) :
    ∃ g : NativeSporadic.M11, g * m11a = m11a * g ∧
      (orderOf (y * (g * y * g⁻¹)) = 4 ∨ orderOf (y * (g * y * g⁻¹)) = 8) := by
  have hmem := m11_mem_invs hy2 hy1
  have h1 := List.all_eq_true.1 m11O4Check_holds _ hmem
  have hyab : ((y : Equiv.Perm (Fin 11)) * m11gA == m11gA * (y : Equiv.Perm (Fin 11))) = true := by
    simpa using congrArg Subtype.val hya
  have hyab' : ((y : Equiv.Perm (Fin 11)) == m11gA) = false := by
    simpa using fun h => hya' (Subtype.ext h)
  simp only [hyab, hyab', Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, Bool.or_eq_true] at h1
  obtain ⟨g, hg, hga, hord⟩ := h1
  have hgm : g ∈ NativeSporadic.M11 := (mem_m11Elements g).1 hg
  refine ⟨⟨g, hgm⟩, Subtype.ext hga, ?_⟩
  rcases hord with h4 | h8
  · left
    rw [m11_orderOf_eq_iff _ (by norm_num)]
    simpa using h4
  · right
    rw [m11_orderOf_eq_iff _ (by norm_num)]
    simpa using h8

theorem sporadicExclusion2F_M11 :
    SporadicExclusion2F .M11 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hL : L ≠ ⊥ := ne_bot_of_isQuasisimple hq
  have e' : CQ L ≃* NativeSporadic.M11 := e
  have hrank := rank_of_generation hW hq.1 hirr hL e' (k := 3) (ρ := 4) (p := 11) (by norm_num)
    (by rw [m11_card]; norm_num) (by norm_num [orderOf_two_zmod_11])
    (fun t ht2 ht1 => m11_gen t ht2 ht1)
  have hEL : E ≤ L := le_of_autInner hW hq.1 hirr hE hEel e' m11_autInner
  have hsqE : ∀ b ∈ E, b * b = 1 := fun b hb => by
    have := hEel.2 b hb
    rwa [sq] at this
  have hrankE : ∀ b ∈ E, b ≠ 1 → 2 ^ 4 ≤ (fixV (Subgroup.zpowers b)).index :=
    fun b hb hb1 => hrank b (hEL hb) hb1 (hsqE b hb)
  have hcard : Nat.card E ≤ 2 ^ 2 :=
    card_le_two_pow_of_le hW hirr hEL hEel e' m11_elemAbelian_le
  by_cases h2 : Nat.card E ≤ 2
  · exact weight2_lt_of_rank hEne (r := 1) (ρ := 4) (by norm_num) (by simpa using h2) hrankE
  refine weight2_lt_of_lt_index E ?_
  by_contra hcon
  push Not at hcon
  have hidx16 : (fixV E).index ≤ 2 ^ 4 :=
    hcon.trans ((Nat.pow_le_pow_left hcard 2).trans (by norm_num))
  obtain ⟨t, htE, u, huE, ht1, hu1, htu⟩ := exists_two_ne_one h2
  have hfix : fixV E = fixV (Subgroup.zpowers t) :=
    fixV_eq_of_index_le htE (hidx16.trans (hrankE t htE ht1))
  set π := redHom L e' with hπ
  have hinjE := redHom_comp_injective hW hirr hEL hEel e'
  have himg : ∀ {x y : MulAut W} (hx : x ∈ E) (hy : y ∈ E), π ⟨x, hEL hx⟩ = π ⟨y, hEL hy⟩ →
      x = y := by
    intro x y hx hy hxy
    have := @hinjE ⟨x, hx⟩ ⟨y, hy⟩ hxy
    exact congrArg Subtype.val this
  have hπ1 : ∀ {x : MulAut W} (hx : x ∈ E), x ≠ 1 → π ⟨x, hEL hx⟩ ≠ 1 := by
    intro x hx hx1 h
    apply hx1
    have h1 := (injective_iff_map_eq_one _).1 hinjE ⟨x, hx⟩ h
    exact congrArg Subtype.val h1
  have hπ2 : ∀ {x : MulAut W} (hx : x ∈ E), π ⟨x, hEL hx⟩ * π ⟨x, hEL hx⟩ = 1 := by
    intro x hx
    rw [← map_mul]
    have : (⟨x, hEL hx⟩ : ↥L) * ⟨x, hEL hx⟩ = 1 := Subtype.ext (hsqE x hx)
    rw [this, map_one]
  have hπc : π ⟨u, hEL huE⟩ * π ⟨t, hEL htE⟩ = π ⟨t, hEL htE⟩ * π ⟨u, hEL huE⟩ := by
    have hut : (⟨u, hEL huE⟩ : ↥L) * ⟨t, hEL htE⟩ = ⟨t, hEL htE⟩ * ⟨u, hEL huE⟩ :=
      Subtype.ext (hEel.1 u huE t htE)
    rw [← map_mul, ← map_mul, hut]
  obtain ⟨h, hh⟩ := m11_exists_conj (hπ2 htE) (hπ1 htE ht1)
  set y : NativeSporadic.M11 := h⁻¹ * π ⟨u, hEL huE⟩ * h with hy
  have hy2 : y * y = 1 := by
    calc y * y = h⁻¹ * (π ⟨u, hEL huE⟩ * π ⟨u, hEL huE⟩) * h := by rw [hy]; group
      _ = 1 := by rw [hπ2 huE]; group
  have hy1 : y ≠ 1 := by
    intro h0
    apply hπ1 huE hu1
    calc π ⟨u, hEL huE⟩ = h * y * h⁻¹ := by rw [hy]; group
      _ = 1 := by rw [h0]; group
  have hya : y * m11a = m11a * y := by
    have hta : π ⟨t, hEL htE⟩ = h * m11a * h⁻¹ := hh.symm
    have hut : π ⟨u, hEL huE⟩ * (h * m11a * h⁻¹) = (h * m11a * h⁻¹) * π ⟨u, hEL huE⟩ := by
      rw [← hta]; exact hπc
    calc y * m11a = h⁻¹ * (π ⟨u, hEL huE⟩ * (h * m11a * h⁻¹)) * h := by rw [hy]; group
      _ = h⁻¹ * ((h * m11a * h⁻¹) * π ⟨u, hEL huE⟩) * h := by rw [hut]
      _ = m11a * y := by rw [hy]; group
  have hya' : y ≠ m11a := by
    intro h0
    apply htu
    apply himg htE huE
    calc π ⟨t, hEL htE⟩ = h * m11a * h⁻¹ := hh.symm
      _ = h * y * h⁻¹ := by rw [h0]
      _ = π ⟨u, hEL huE⟩ := by rw [hy]; group
  obtain ⟨g₀, hg₀a, hord⟩ := m11_o4 hy2 hy1 hya hya'
  set gb : NativeSporadic.M11 := h * g₀ * h⁻¹ with hgb
  have hgbt : gb * π ⟨t, hEL htE⟩ = π ⟨t, hEL htE⟩ * gb := by
    rw [← hh, hgb]
    calc h * g₀ * h⁻¹ * (h * m11a * h⁻¹) = h * (g₀ * m11a) * h⁻¹ := by group
      _ = h * (m11a * g₀) * h⁻¹ := by rw [hg₀a]
      _ = h * m11a * h⁻¹ * (h * g₀ * h⁻¹) := by group
  have hconj : π ⟨u, hEL huE⟩ * (gb * π ⟨u, hEL huE⟩ * gb⁻¹) =
      h * (y * (g₀ * y * g₀⁻¹)) * h⁻¹ := by
    rw [hgb, hy]; group
  have hord' : orderOf (π ⟨u, hEL huE⟩ * (gb * π ⟨u, hEL huE⟩ * gb⁻¹)) = 4 ∨
      orderOf (π ⟨u, hEL huE⟩ * (gb * π ⟨u, hEL huE⟩ * gb⁻¹)) = 8 := by
    rw [hconj, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hord
  obtain ⟨n, hn4, hn2⟩ := exists_pow_order_four_of hord'
  refine false_of_o4_witness hW hirr e' hEL htE huE (hsqE t htE) hfix hgbt n hn4 hn2 ?_
  intro b hb hb1 hb2
  have hidxt : (fixV (Subgroup.zpowers t)).index = (fixV E).index := by rw [hfix]
  rw [hidxt]
  exact hidx16.trans (hrank b hb hb1 hb2)

end CFSG.Quasithin.B45Exc
