module

public import CFSG.Quasithin.Vol2.KGFactG2RuE64
public import CFSG.Quasithin.Vol2.KGFactG2RuLocal
public import CFSG.Quasithin.Vol2.KGFactG2RuAbsK
public import CFSG.Quasithin.Vol2.KGFactG2RuAbsF
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213KG
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213KGRu
public import CFSG.Sporadic.Schreier.RuIso

public noncomputable section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Sporadic.RuSchreier

theorem exists_conj_le_ruS
    {X : Subgroup (Equiv.Perm (Fin 4060))} (hXP : X ≤ ruP) (hX : IsPGroup 2 X) :
    ∃ g ∈ ruP, X.map (MulAut.conj g).toMonoidHom ≤ ruS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (X.subgroupOf ruP) := hX.comap_of_injective ruP.subtype ruP.subtype_injective
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥ruP Q ruSylow
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (⟨x, hXP hx⟩ : ↥ruP) ∈ X.subgroupOf ruP := Subgroup.mem_subgroupOf.2 hx
  have hmem : MulAut.conj g • (⟨x, hXP hx⟩ : ↥ruP) ∈ (ruSylow : Subgroup ↥ruP) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ hx')
  rw [ruSylow_coe, Subgroup.mem_subgroupOf, MulAut.smul_def, MulAut.conj_apply] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem ruG2Model :
    G2RuModel ruP ruS g2W g2V g2X [g2N 0, g2N 1] g2A where
  T_le := ruS_le
  sylow := fun _ hXP hX => exists_conj_le_ruS hXP hX
  W_le := g2W_le
  W_sq := fun _ hw => g2W_sq hw
  card_W := card_g2W_le
  e64 := fun E hET hE hcard => by
    obtain ⟨r, -, hr⟩ := le_g2Wr_of_card hET hE hcard
    exact ⟨g2Sigma r, g2Sigma_mem r, hr⟩
  card_N := card_ruP_inf_normalizer_le
  V_le := g2V_le_g2W
  card_V := card_g2V
  T_V := fun _ hs hW => normalizer_V_of_mem_ruS hs hW
  x_mem := g2X_mem
  x_comm := fun _ hv => g2X_comm hv
  x_not := g2X_not_mem
  n_mem := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact g2N_spec (by norm_num)
    · exact g2N_spec (by norm_num)
  n_gen := g2V_le_closure
  a_mem := fun _ hi => (g2A_spec hi).1
  a_V := fun _ hi => (g2A_spec hi).2.1
  a_sq := fun _ hi => (g2A_spec hi).2.2
  a_comm := fun _ hi _ hj _ hw => g2A_comm hi hj hw
  a_ne := fun _ he _ he' hne => g2AElt_ne he he' hne

theorem exists_map_ruP
    {G : Type} [Group G] {K : Subgroup G}
    (hRu : IsSporadic .Ru (↥K ⧸ Subgroup.center ↥K)) :
    ∃ ψ : ↥K →* Equiv.Perm (Fin 4060), ψ.range = ruP ∧ ψ.ker = Subgroup.center ↥K := by
  obtain ⟨e₀⟩ := hRu
  let e : ↥K ⧸ Subgroup.center ↥K ≃* ↥ruP := e₀.trans ruEquivP
  refine ⟨ruP.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' _)), ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
      (e.surjective.comp (QuotientGroup.mk'_surjective _)), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      OneMemClass.coe_eq_one, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem kgG2BlockRu_holds :
    KGG2BlockRu := by
  intro G _ _ K B S W _ hRu hBK hB hS hWU hBW hW
  obtain ⟨ψ, hrange, hker⟩ := exists_map_ruP hRu
  exact kgg2_of_model ruG2Model hrange hker hBK hB hS hWU hBW hW

theorem kgG2BlockRuFF_holds :
    KGG2BlockRuFF := by
  intro G _ _ K B W _ hRu hBK hB hWU hWZ hBW hW
  obtain ⟨ψ, hrange, hker⟩ := exists_map_ruP hRu
  exact ff_of_model ruG2Model hrange hker hBK hB hWU hWZ hBW hW

end CFSG.Quasithin.H13.Ch4.G2Ru
