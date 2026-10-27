module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Cent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2UC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2Fin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpEnd

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp2

open S35.Ch2 S35.Fin S35.Lp
open S34 (Cb)
open S35.II (That2)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem conjSub_fixSecIn' (g : G) (A L N : Subgroup G) :
    conjSub g (fixSecIn A L N) = fixSecIn (conjSub g A) (conjSub g L) (conjSub g N) := by
  unfold fixSecIn
  rw [conjSub_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxa⟩, rfl⟩
    refine ⟨mul_mem_conjSub hx, fun a' ha' => ?_⟩
    have ha := mem_conjSub.mp ha'
    have h1 := mul_mem_conjSub (g := g) (hxa _ ha)
    have e : g * (g⁻¹ * a' * g * x * (g⁻¹ * a' * g)⁻¹ * x⁻¹) * g⁻¹ =
        a' * (g * x * g⁻¹) * a'⁻¹ * (g * x * g⁻¹)⁻¹ := by group
    rwa [e] at h1
  · rintro ⟨hy, hya⟩
    refine ⟨g⁻¹ * y * g, ⟨mem_conjSub.mp hy, fun a ha => ?_⟩, by group⟩
    have h1 := mem_conjSub.mp (hya (g * a * g⁻¹) (mul_mem_conjSub ha))
    have e : g⁻¹ * (g * a * g⁻¹ * y * (g * a * g⁻¹)⁻¹ * y⁻¹) * g =
        a * (g⁻¹ * y * g) * a⁻¹ * (g⁻¹ * y * g)⁻¹ := by group
    rwa [e] at h1

omit [Finite G] in
theorem secIdx_conjSub' (g : G) (A L N : Subgroup G) :
    secIdx (conjSub g A) (conjSub g L) (conjSub g N) = secIdx A L N := by
  unfold secIdx
  rw [← conjSub_fixSecIn']
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

omit [Finite G] in
theorem conjSub_zpowers' (g x : G) :
    conjSub g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) :=
  MonoidHom.map_zpowers _ x

omit [Finite G] in
theorem rk_smul (g : ↥(H ⊔ M)) (δ : Geo H M) (y : G) :
    S34.rk (g • δ) ((g : G) * y * (g : G)⁻¹) = S34.rk δ y := by
  unfold S34.rk
  rw [S34.Cb_smul, Vn_smul, ← conjSub_zpowers', secIdx_conjSub']

theorem That2_le_of_rk (hS : Sit H M S) {δ l ρ : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) (hρl : l ∈ nbrs ρ) {t : G} (ht : t ∈ Qv δ ⊓ Qv l)
    (htρ : S34.rk ρ t = 2) : That2 ρ l ≤ (Qv δ ⊓ Qv l) ⊔ Qv ρ := by
  have hlv : vtype l = true := Std.vtype_nbr_S5 hδ hl
  have hlρ : ρ ∈ nbrs l := Std.mem_nbrs_symm.mp hρl
  have hρ : vtype ρ = false := Std.vtype_nbr_S3 hlv hlρ
  obtain ⟨c⟩ := exists_chart2 hS hρ
  have hδl : δ ∈ nbrs l := Std.mem_nbrs_symm.mp hl
  set N : Subgroup G := Qv δ ⊓ Qv l with hN
  have hQlρ : Qv l ≤ stab ρ := Std.Qv_le_stab hS hlρ
  have hNs : N ≤ stab ρ ⊓ stab l :=
    le_inf (inf_le_right.trans hQlρ) (inf_le_right.trans (Ch.Qv_le_stab' l))
  have hts : t ∈ stab ρ := hQlρ ht.2
  have hsw : (c.θ ⟨t, hts⟩).IsSwap := by
    have h1 : S34.rk ρ t = idx orth (c.θ ⟨t, hts⟩) := c.rk_eq_idx hts
    rw [htρ] at h1
    exact (idx_orth_eq_two_iff _).mp h1.symm
  have hD : Nat.card (c.Dl l) = 8 := c.card_Dl hS hρl
  have hB : c.bar N ≤ c.Dl l := c.bar_mono hNs
  have hnorm : ∀ q ∈ Qv l, ∀ n ∈ N, q * n * q⁻¹ ∈ N := by
    intro q hq n hn
    refine ⟨?_, (Qv l).mul_mem ((Qv l).mul_mem hq hn.2) ((Qv l).inv_mem hq)⟩
    have hqs : q ∈ stab δ := Std.Qv_le_stab hS hδl hq
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab δ) hqs) n).mp hn.1
  have hQnorm : Qv l ≤ c.preθ (Subgroup.normalizer ((c.bar N : Subgroup (Perm (Fin 5))) :
      Set (Perm (Fin 5)))) := by
    intro q hq
    refine (c.mem_preθ_iff ⟨q, hQlρ hq⟩).mpr ?_
    refine mem_normalizer_of_forall (fun u hu => ?_) (fun u hu => ?_)
    · obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hu
      refine (c.mem_bar_iff).mpr ⟨⟨q, hQlρ hq⟩ * a * ⟨q, hQlρ hq⟩⁻¹, ?_, by simp⟩
      exact hnorm q hq _ ha
    · obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hu
      refine (c.mem_bar_iff).mpr ⟨⟨q, hQlρ hq⟩⁻¹ * a * ⟨q, hQlρ hq⟩⁻¹⁻¹, ?_, by simp⟩
      exact hnorm q⁻¹ ((Qv l).inv_mem hq) _ ha
  have hnorm' : ∀ d ∈ c.Dl l, ∀ b ∈ c.bar N, d * b * d⁻¹ ∈ c.bar N := by
    intro d hd b hb
    obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hd
    have h1 : (a : G) ∈ Qv ρ ⊔ Qv l := (Std.stab_inf_eq hS hρ hρl) ▸ ha
    have h2 : (a : G) ∈ c.preθ (Subgroup.normalizer ((c.bar N : Subgroup (Perm (Fin 5))) :
        Set (Perm (Fin 5)))) :=
      sup_le (c.Qv_le_preθ hS hρ _) hQnorm h1
    exact (Subgroup.mem_normalizer_iff.mp ((c.mem_preθ_iff a).mp h2) b).mp hb
  have hT : That (c.Dl l) ≤ c.bar N :=
    That_le_of_normal hD hB hnorm' (c.mem_bar_of_mem (a := t) ht (hts)) hsw
  intro x hx
  have hxθ := c.That2_le_preθ hS hρ hρl hx
  have hxs : x ∈ stab ρ := c.preθ_le_stab _ hxθ
  have hxT : c.θ ⟨x, hxs⟩ ∈ c.bar N := hT ((c.mem_preθ_iff ⟨x, hxs⟩).mp hxθ)
  obtain ⟨a, ha, hax⟩ := (c.mem_bar_iff).mp hxT
  have hq : (a : G)⁻¹ * x ∈ Qv ρ := by
    have : c.θ (a⁻¹ * ⟨x, hxs⟩) = 1 := by rw [map_mul, map_inv, hax, inv_mul_cancel]
    exact (c.ker_iff hS hρ _).mp this
  have e : x = (a : G) * ((a : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup ha hq

theorem nbarThat_II (hS : Sit H M S) (_hII : CaseII H M) (hLP : ClaimLP H M) :
    S35.II.NbarThat H M := by
  have hU : ∀ δ : Geo H M, vtype δ = false → UC δ := fun δ hδ => UC.of_sit hS hδ
  obtain ⟨β, α', hp, v, hv, hvs, hv2⟩ := hLP
  obtain ⟨m, γ', hm, hγ, h1, h2, hVle, -, -⟩ := Std.PD_geodesic hS hp
  have hb : Back H M β α' m γ' := ⟨hm, hγ, h1, h2⟩
  have hvQ : v ∈ Qv γ' ⊓ Qv m := ⟨(hVle hv).2, (hVle hv).1⟩
  have hrk : S34.rk α' v = 2 := by
    unfold S34.rk
    rw [← secIdx_Zv_eq_Cb (hU _ hp.vδ') (Zv_le_Cb' hS hp.vδ') hvs]
    exact hv2
  intro δ l ρ hδ hl hρl hne
  have hlv := Std.vtype_nbr_S5 hδ hl
  have hρ : vtype ρ = false := Std.vtype_nbr_S3 hlv (Std.mem_nbrs_symm.mp hρl)
  obtain ⟨g, hg1, hg2, hg3⟩ := Std.arc_trans hS hp.vδ' hb.1 (Std.mem_nbrs_symm.mp hb.2.1)
    (back_ne hp hb) hρ hρl hl (Ne.symm hne)
  subst hg1 hg2 hg3
  have ht : (g : G) * v * (g : G)⁻¹ ∈ Qv (g • γ') ⊓ Qv (g • m) := by
    rw [Qv_smul, Qv_smul]
    exact ⟨mul_mem_conjSub hvQ.1, mul_mem_conjSub hvQ.2⟩
  exact That2_le_of_rk hS hδ hl hρl ht (by rw [rk_smul]; exact hrk)

end S35.Lp2

end F53.Stellmacher

end CFSG.Quasithin
