module

public import CFSG.Quasithin.Background.F918V2BA
public import CFSG.Quasithin.Background.F918V2F
public import CFSG.Quasithin.Background.F918V2G3
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

namespace Z391

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem v2g_final (hD : D3Std M L T L V)
    {Q : Type} [CommGroup Q] [MulDistribMulAction ↥M Q] (π : W →* Q)
    (hπs : Function.Surjective π)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (hker : π.ker = fixV L)
    (t : ↥M) (htT : (t : MulAut W) ∈ T)
    (hTT : TwoType (L.subgroupOf M) (T.subgroupOf M) (V.map π) t)
    {S₀ : Subgroup Q} (hS₀ : XMod.IsIrr ↥(L.subgroupOf M) S₀)
    (hS₀iso : XMod.Iso ↥(L.subgroupOf M) S₀ (V.map π)) (hS₀d : V.map π ⊓ S₀ = ⊥)
    (hdec : (V.map π ⊔ S₀) ⊔ t • (V.map π ⊔ S₀) = ⊤)
    (hdis : (V.map π ⊔ S₀) ⊓ t • (V.map π ⊔ S₀) = ⊥)
    (hall : ∀ R : Subgroup Q, XMod.IsIrr ↥(L.subgroupOf M) R →
      XMod.Iso ↥(L.subgroupOf M) R (V.map π) → R ≤ V.map π ⊔ S₀)
    (hE1 : EndUnitsTrivial (L.subgroupOf M) (V.map π))
    (hE2 : EndUnitsTrivial (L.subgroupOf M) (t • V.map π))
    (hOnto : AutFromGroup (L.subgroupOf M) (V.map π))
    (hFaith : FaithfulOn (L.subgroupOf M) (V.map π))
    (hYE : ∀ c : MulAut W, c ∈ M → c ^ 3 = 1 → (∀ l ∈ L, c * l = l * c) → c = 1) :
    orbSup T V = ⊤ := by
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hC0 : ∀ c : MulAut W, c ∈ M → (∀ l ∈ L, c * l = l * c) → c = 1 := by
    let C₀ : Subgroup (MulAut W) :=
      { carrier := {c | c ∈ M ∧ ∀ l ∈ L, c * l = l * c}
        one_mem' := ⟨M.one_mem, fun l _ => by simp⟩
        mul_mem' := by
          rintro a b ⟨haM, haL⟩ ⟨hbM, hbL⟩
          refine ⟨M.mul_mem haM hbM, fun l hl => ?_⟩
          rw [mul_assoc, hbL l hl, ← mul_assoc, haL l hl, mul_assoc]
        inv_mem' := by
          rintro a ⟨haM, haL⟩
          refine ⟨M.inv_mem haM, fun l hl => ?_⟩
          have h := haL l hl
          calc a⁻¹ * l = a⁻¹ * (l * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * l) * a⁻¹ := by rw [h]
            _ = l * a⁻¹ := by group }
    have hC₀M : C₀ ≤ M := fun x hx => hx.1
    have hkey : ∀ g ∈ M, ∀ x ∈ C₀, g * x * g⁻¹ ∈ C₀ := by
      rintro g hg x ⟨hxM, hxL⟩
      refine ⟨M.mul_mem (M.mul_mem hg hxM) (M.inv_mem hg), fun l hl => ?_⟩
      have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L := hMn g⁻¹ (M.inv_mem hg) l hl
      have h := hxL _ hl'
      calc g * x * g⁻¹ * l = g * (x * (g⁻¹ * l * g⁻¹⁻¹)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * l * g⁻¹⁻¹) * x) * g⁻¹ := by rw [h]
        _ = l * (g * x * g⁻¹) := by group
    have hnorm : M ≤ Subgroup.normalizer (C₀ : Set (MulAut W)) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hkey g hg h hh, fun hh => ?_⟩
      have := hkey g⁻¹ (M.inv_mem hg) _ hh
      have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rwa [e] at this
    have hp2 : IsPGroup 2 C₀ := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [IsPGroup.iff_orderOf]
      intro x
      have hx0 : orderOf (x : MulAut W) ≠ 0 := (orderOf_pos _).ne'
      refine ⟨(orderOf (x : MulAut W)).primeFactorsList.length, ?_⟩
      rw [Subgroup.orderOf_coe x |>.symm]
      refine Nat.eq_prime_pow_of_unique_prime_dvd hx0 (fun {d} hd hdvd => ?_)
      by_contra hd2
      set c' : MulAut W := (x : MulAut W) ^ (orderOf (x : MulAut W) / d) with hc'
      have hc'o : orderOf c' = d := orderOf_pow_orderOf_div hx0 hdvd
      have hc'C : c' ∈ C₀ := C₀.pow_mem x.2 _
      have hc'1 : c' ≠ 1 := fun h => by
        rw [h, orderOf_one] at hc'o
        exact hd.one_lt.ne hc'o
      have hdpow : c' ^ d = 1 := hc'o ▸ pow_orderOf_eq_one c'
      rcases Nat.lt_or_ge d 5 with hlt | hge
      · have h3 : d = 3 := by
          have h2lt : 2 < d := lt_of_le_of_ne hd.two_le (Ne.symm hd2)
          interval_cases d
          · rfl
          · exact absurd hd (by norm_num)
        subst h3
        exact hc'1 (hYE c' hc'C.1 hdpow hc'C.2)
      · have hcM : (⟨c', hc'C.1⟩ : ↥M) ^ d = 1 := Subtype.ext (by simpa using hdpow)
        have hcΛ : ∀ l ∈ L.subgroupOf M, (⟨c', hc'C.1⟩ : ↥M) * l = l * ⟨c', hc'C.1⟩ :=
          fun l hl => Subtype.ext (hc'C.2 (l : MulAut W) (Subgroup.mem_subgroupOf.mp hl))
        have : Finite Q := Finite.of_surjective π hπs
        have hfix := centralizer_prime_ge_five hTT hS₀ hS₀iso hS₀d hdec hdis hall hE1 hE2 hcΛ hd
          hge hcM
        refine absurd (v2g_faithful_on_Q hD hc'C.1 hc'C.2 fun w => ?_) hc'1
        have h1 : π (c' w) = π w := by
          have := hfix (π w)
          rwa [hπM] at this
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    have hbot : C₀ ≤ pCoreOf 2 M := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hC₀M hnorm hp2
    rw [D31.pCoreOf_eq_bot hD.hyp] at hbot
    intro c hcM hcL
    exact Subgroup.mem_bot.1 (hbot ⟨hcM, hcL⟩)
  have hN : XMod.Normalizes ↥(L.subgroupOf M) ↥M Q := normalizes_whole _ hTT.normal
  have hstep : ∀ g : ↥M, XMod.Iso ↥(L.subgroupOf M) (g • V.map π) (V.map π) →
      (g : MulAut W) ∈ L := by
    intro g hg
    obtain ⟨h, hh⟩ := iso_realized_of_iso hTT.normal hg
    obtain ⟨l₀, hl₀, hl₀h⟩ := hOnto h
    have hinv := hTT.irr.1
    have key : ∀ l : ↥M, l ∈ L.subgroupOf M → g⁻¹ * l₀ * l = l * (g⁻¹ * l₀) := by
      intro l hl
      have hm : (l₀ * l)⁻¹ * (g * l * g⁻¹) * l₀ ∈ L.subgroupOf M :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hl₀ hl))
          (hTT.normal g l hl)) hl₀
      have h1 : ∀ x ∈ V.map π, ((l₀ * l)⁻¹ * (g * l * g⁻¹) * l₀) • x = x := by
        intro x hx
        have hlx : l • x ∈ V.map π := hinv ⟨l, hl⟩ x hx
        have h2 := hh ⟨l, hl⟩ ⟨x, hx⟩ ⟨l • x, hlx⟩ rfl
        rw [hl₀h ⟨x, hx⟩, hl₀h ⟨l • x, hlx⟩] at h2
        have h3 : (g * l * g⁻¹ * l₀) • x = (l₀ * l) • x := by
          calc (g * l * g⁻¹ * l₀) • x = (g * l * g⁻¹) • l₀ • x := mul_smul _ _ _
            _ = l₀ • l • x := h2
            _ = (l₀ * l) • x := (mul_smul _ _ _).symm
        have e : ((l₀ * l)⁻¹ * (g * l * g⁻¹) * l₀) • x =
            (l₀ * l)⁻¹ • (g * l * g⁻¹ * l₀) • x := by
          rw [mul_assoc, mul_smul]
        rw [e, h3, inv_smul_smul]
      have h4 := hFaith _ hm h1
      have h5 : g * l * g⁻¹ * l₀ = l₀ * l := by
        have := congrArg (fun z => (l₀ * l) * z) h4
        simpa [mul_assoc] using this
      calc g⁻¹ * l₀ * l = g⁻¹ * (g * l * g⁻¹ * l₀) := by rw [h5, mul_assoc]
        _ = l * (g⁻¹ * l₀) := by group
    have hc1 := hC0 ((g⁻¹ * l₀ : ↥M) : MulAut W) (g⁻¹ * l₀).2 fun l hl => by
      have := congrArg (fun z : ↥M => (z : MulAut W))
        (key ⟨l, hLM hl⟩ (Subgroup.mem_subgroupOf.mpr hl))
      exact this
    have hg1 : (g : MulAut W) = (l₀ : MulAut W) := by
      have : g⁻¹ * l₀ = 1 := Subtype.ext hc1
      have := congrArg (fun z : ↥M => g * z) this
      simpa using this.symm
    rw [hg1]
    exact Subgroup.mem_subgroupOf.mp hl₀
  refine top_unique ?_
  rw [← hD.hyp.gen]
  refine iSup₂_le fun m hm => ?_
  have hVL : ∀ l ∈ L, V.map l.toMonoidHom = V := fun l hl => by
    obtain ⟨hVinv, -, -, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
    exact mem_stabSub_iff_map_eq.mp (B1.le_stabSub_of_invariant hVinv hl)
  rcases hTT.types ⟨m, hm⟩ with h1 | h2
  · have := hstep ⟨m, hm⟩ h1
    rw [hVL m this]
    exact le_orbSup T V
  · have h3 := hstep (t⁻¹ * ⟨m, hm⟩) (by
      have := XMod.iso_smul hN t⁻¹ h2
      rwa [← mul_smul, inv_smul_smul] at this)
    have hm' : m = (t : MulAut W) * (((t⁻¹ * ⟨m, hm⟩ : ↥M)) : MulAut W) := by
      simp
    rw [hm', CFSG.Quasithin.map_mul_aut', hVL _ h3]
    exact map_le_orbSup htT

end Z391

end CFSG.Quasithin
