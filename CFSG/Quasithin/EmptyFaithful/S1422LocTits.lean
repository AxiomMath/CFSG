module

public import CFSG.Quasithin.EmptyFaithful.S1422LocTitsGrp
public import CFSG.Quasithin.EmptyFaithful.S1422LocTitsAct
public import CFSG.Quasithin.EmptyFaithful.S1422LocTitsDefs
public import CFSG.Quasithin.EmptyFaithful.S1422LocTitsKer
public import CFSG.Quasithin.EmptyFaithful.S1422Sz

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.S1422Loc

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem titsLike_local (hSz : Nat.card ↥(Sz 0) = 20) (S : Setting1422 T M Y H)
    (hq : Nonempty (oTwoQuot ↥H ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H ≃* ↥(Sz 0)))
    (hF : TitsLikeVertexFacts H (Y ⊔ T)) :
    H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨E, F, hEmem, hFmem, hEsq, hEab, hPF16, hFE2, hCE, hPP, hlat, ⟨j₀, hj₀P, hj₀F, hj₀sq⟩,
    htrans, c, hcH, hc5, hcfpf⟩ := hF
  obtain ⟨z, hz, hz1, hz2, hZ⟩ := S.exists_z
  have hHT := S.H_inf_YT hSz
  rw [hHT] at hEmem hCE hlat
  set Mc : Subgroup G := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hMcdef
  set P : Subgroup G := pCoreOf 2 H with hPdef
  set Z : Subgroup G := quasithinOmegaOneCenter T with hZdef
  set Q : Subgroup G := pCoreOf 2 Mc with hQdef
  have hEP : E ≤ P := fun x hx => ((hEmem x).mp hx).1
  have hEZ : ∀ e ∈ E, ∀ y ∈ P, e * y * e⁻¹ * y⁻¹ ∈ Z := fun e he => ((hEmem e).mp he).2
  have hFP : F ≤ P := fun x hx => ((hFmem x).mp hx).1
  have hFE' : ∀ u ∈ F, ∀ e ∈ E, u * e = e * u := fun u hu => ((hFmem u).mp hu).2
  have hEF : E ≤ F := fun e he => (hFmem e).mpr ⟨hEP he, fun e' he' => hEab e he e' he'⟩
  have hHMc : H ≤ Mc := S.H_le_centralizer
  have hPH : P ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hPMc : P ≤ Mc := hPH.trans hHMc
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Mc
  have hQP : Q ≤ P := S.pCoreOf_Mc_le
  have hQMc : Q ≤ Mc := CFSG.LieType.BorelTits.pCoreOf_le 2 Mc
  have hMcQ : Mc ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Mc
  have hZ2 : IsPGroup 2 Z :=
    IsPGroup.of_card (n := 1) (by rw [S.hyp.card_omegaOneCenter]; norm_num)
  have hZcen : ∀ w ∈ Z, ∀ x ∈ P, x * w = w * x := fun w hw x hx => mem_Mc_comm hw (hPMc hx)
  have hconjZ : ∀ g ∈ Mc, ∀ w ∈ Z, g * w * g⁻¹ = w := by
    intro g hg w hw
    have := mem_Mc_comm hw hg
    rw [this]; group
  have hgQ : ∀ g ∈ Mc, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hMcQ hg) x).mp hx
  have hEQ : E ≤ Q := fun x hx =>
    S.mem_pCoreOf_Mc_of_comm_mem (hPMc (hEP hx)) fun q hq' => hEZ x hx q (hQP hq')
  have hMcE : ∀ g ∈ Mc, ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    intro g hg x hx
    rcases hlat Q hEQ hQP (hHMc.trans hMcQ) with ha | hb
    · refine ha _ (hgQ g hg x (hEQ hx)) fun y hy => ?_
      have hgy : g⁻¹ * y * g ∈ Q := by
        have := hgQ g⁻¹ (Mc.inv_mem hg) y hy
        simpa using this
      have h1 := hEZ x hx _ (hQP hgy)
      have h2 : (g * x * g⁻¹) * y * (g * x * g⁻¹)⁻¹ * y⁻¹ =
          g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
      rw [h2, hconjZ g hg _ h1]
      exact h1
    · refine hb _ (hgQ g hg x (hEQ hx)) ?_
      calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hEsq x hx]; group
  have hMcEn : Mc ≤ Subgroup.normalizer (E : Set G) := le_normalizer_of_forall_conj_mem hMcE
  set N : Subgroup G := Mc ⊓ Subgroup.centralizer (E : Set G) with hNdef
  have hMcN : Mc ≤ Subgroup.normalizer (N : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun g hg n hn => ?_
    refine ⟨Mc.mul_mem (Mc.mul_mem hg hn.1) (Mc.inv_mem hg), Subgroup.mem_centralizer_iff.mpr
      fun e he => ?_⟩
    have he'' : g⁻¹ * e * g ∈ E := by
      have := hMcE g⁻¹ (Mc.inv_mem hg) e he
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hn.2 _ he''
    calc e * (g * n * g⁻¹) = g * ((g⁻¹ * e * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
      _ = (g * n * g⁻¹) * e := by group
  set C : Subgroup G := Q ⊓ Subgroup.centralizer (E : Set G) with hCdef
  have hEC : E ≤ C := fun e he => ⟨hEQ he, Subgroup.mem_centralizer_iff.mpr fun e' he' =>
    hEab e' he' e he⟩
  have hCF : C ≤ F := fun x hx => (hFmem x).mpr ⟨hQP hx.1, fun e he =>
    (Subgroup.mem_centralizer_iff.mp hx.2 e he).symm⟩
  have hCP : C ≤ P := hCF.trans hFP
  have hMcC : ∀ m ∈ Mc, ∀ x ∈ C, m * x * m⁻¹ ∈ C := by
    intro m hm x hx
    refine ⟨hgQ m hm x hx.1, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    have he'' : m⁻¹ * e * m ∈ E := by
      have := hMcE m⁻¹ (Mc.inv_mem hm) e he
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ he''
    calc e * (m * x * m⁻¹) = m * ((m⁻¹ * e * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * e * m)) * m⁻¹ := by rw [h1]
      _ = (m * x * m⁻¹) * e := by group
  have hMcCn : Mc ≤ Subgroup.normalizer (C : Set G) := le_normalizer_of_forall_conj_mem hMcC
  have hN2 : IsPGroup 2 N := by
    refine isPGroup_two_of_odd_eq_one fun g hg hodd => ?_
    obtain ⟨hgMc, hgC⟩ := hg
    have hgE : ∀ e ∈ E, g * e = e * g := fun e he =>
      (Subgroup.mem_centralizer_iff.mp hgC e he).symm
    have hstepC : ∀ f ∈ C, g * f * g⁻¹ * f⁻¹ ∈ E := by
      intro f hf
      have h := card_eq_card_mul_relIndex hEC
      have hCle : Nat.card C ≤ Nat.card F := Subgroup.card_le_of_le hCF
      have hEpos : 0 < Nat.card E := Nat.card_pos
      have hr1 : E.relIndex C ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at h
        exact (Nat.card_pos (α := C)).ne' h
      have hr2 : E.relIndex C ≤ 2 := by
        by_contra hcon
        have h3 : 3 ≤ E.relIndex C := by omega
        have h4 : Nat.card E * 3 ≤ Nat.card E * E.relIndex C := Nat.mul_le_mul_left _ h3
        omega
      have hr : E.relIndex C = 1 ∨ E.relIndex C = 2 := by omega
      rcases hr with hr | hr
      · have hCE' : C ≤ E := Subgroup.relIndex_eq_one.mp hr
        exact hCE' (C.mul_mem (hMcC g hgMc f hf) (C.inv_mem hf))
      · exact conj_comm_mem_of_relIndex_two hr (hMcEn hgMc) (hMcCn hgMc) hf
    have hcC : ∀ f ∈ C, g * f = f * g :=
      commutes_of_step_of_odd hodd (hP2.to_le hEP) hgE hstepC
    have hstepQ : ∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ C := by
      intro q hq'
      have hyQ : q⁻¹ * (g * q * g⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hq') (hgQ g hgMc q hq')
      have hyC : q⁻¹ * (g * q * g⁻¹) ∈ C := by
        refine ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
        have hζ : e * q * e⁻¹ * q⁻¹ ∈ Z := hEZ e he q (hQP hq')
        obtain ⟨ζ, hζdef⟩ : ∃ ζ : G, ζ = e * q * e⁻¹ * q⁻¹ := ⟨_, rfl⟩
        rw [← hζdef] at hζ
        have hζi : ζ⁻¹ ∈ Z := Z.inv_mem hζ
        have hgζi : g * ζ⁻¹ = ζ⁻¹ * g := mem_Mc_comm hζi hgMc
        have hqζi : q * ζ⁻¹ = ζ⁻¹ * q := mem_Mc_comm hζi (hQMc hq')
        have hqζ : q * ζ = ζ * q := mem_Mc_comm hζ (hQMc hq')
        have hge : g * e = e * g := hgE e he
        have hge' : g⁻¹ * e = e * g⁻¹ := by
          calc g⁻¹ * e = g⁻¹ * (e * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * e) * g⁻¹ := by rw [hge]
            _ = e * g⁻¹ := by group
        have hC : q * e = ζ⁻¹ * (e * q) := by rw [hζdef]; group
        have hqi : q⁻¹ * ζ⁻¹ = ζ⁻¹ * q⁻¹ := by
          calc q⁻¹ * ζ⁻¹ = q⁻¹ * (ζ⁻¹ * q) * q⁻¹ := by group
            _ = q⁻¹ * (q * ζ⁻¹) * q⁻¹ := by rw [hqζi]
            _ = ζ⁻¹ * q⁻¹ := by group
        have hB : q⁻¹ * e = ζ * (e * q⁻¹) := by
          have h1 : q⁻¹ * e * q * e⁻¹ = ζ := by
            calc q⁻¹ * e * q * e⁻¹ = q⁻¹ * (e * q * e⁻¹ * q⁻¹) * q := by group
              _ = q⁻¹ * ζ * q := by rw [← hζdef]
              _ = ζ := by
                calc q⁻¹ * ζ * q = q⁻¹ * (ζ * q) := by group
                  _ = q⁻¹ * (q * ζ) := by rw [hqζ]
                  _ = ζ := by group
          calc q⁻¹ * e = (q⁻¹ * e * q * e⁻¹) * (e * q⁻¹) := by group
            _ = ζ * (e * q⁻¹) := by rw [h1]
        have hA : (g * q * g⁻¹) * e = ζ⁻¹ * (e * (g * q * g⁻¹)) := by
          calc (g * q * g⁻¹) * e = g * q * (g⁻¹ * e) := by group
            _ = g * q * (e * g⁻¹) := by rw [hge']
            _ = g * (q * e) * g⁻¹ := by group
            _ = g * (ζ⁻¹ * (e * q)) * g⁻¹ := by rw [hC]
            _ = (g * ζ⁻¹) * (e * q) * g⁻¹ := by group
            _ = (ζ⁻¹ * g) * (e * q) * g⁻¹ := by rw [hgζi]
            _ = ζ⁻¹ * ((g * e) * q * g⁻¹) := by group
            _ = ζ⁻¹ * ((e * g) * q * g⁻¹) := by rw [hge]
            _ = ζ⁻¹ * (e * (g * q * g⁻¹)) := by group
        calc e * (q⁻¹ * (g * q * g⁻¹)) = (e * q⁻¹) * (g * q * g⁻¹) := by group
          _ = ζ⁻¹ * (ζ * (e * q⁻¹)) * (g * q * g⁻¹) := by group
          _ = ζ⁻¹ * (q⁻¹ * e) * (g * q * g⁻¹) := by rw [← hB]
          _ = ζ⁻¹ * q⁻¹ * e * (g * q * g⁻¹) := by group
          _ = q⁻¹ * ζ⁻¹ * e * (g * q * g⁻¹) := by rw [← hqi]
          _ = q⁻¹ * (ζ⁻¹ * (e * (g * q * g⁻¹))) := by group
          _ = q⁻¹ * ((g * q * g⁻¹) * e) := by rw [← hA]
          _ = (q⁻¹ * (g * q * g⁻¹)) * e := by group
      have e1 : g * q * g⁻¹ * q⁻¹ = q * (q⁻¹ * (g * q * g⁻¹)) * q⁻¹ := by group
      rw [e1]
      exact hMcC q (hQMc hq') _ hyC
    have hcQ : ∀ q ∈ Q, g * q = q * g :=
      commutes_of_step_of_odd hodd (hP2.to_le hCP) hcC hstepQ
    have hmem : g ∈ pCoreOf 2 Mc :=
      S.charTwo_Mc ⟨hgMc, Subgroup.mem_centralizer_iff.mpr fun q hq' => (hcQ q hq').symm⟩
    exact eq_one_of_odd_of_mem_pCoreOf hmem hodd
  have hNQ : N ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hMcN hN2
  let D : Subgroup G :=
    { carrier := {y | y ∈ Mc ∧ ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Z}
      one_mem' := ⟨Mc.one_mem, fun e _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
        refine ⟨Mc.mul_mem ha hb, fun e he => ?_⟩
        have h1 := hac e he
        have h2 := hbc e he
        have h3 : a * b * e * (a * b)⁻¹ * e⁻¹ =
            (a * (b * e * b⁻¹ * e⁻¹) * a⁻¹) * (a * e * a⁻¹ * e⁻¹) := by group
        rw [h3, hconjZ a ha _ h2]
        exact Z.mul_mem h2 h1
      inv_mem' := by
        rintro a ⟨ha, hac⟩
        refine ⟨Mc.inv_mem ha, fun e he => ?_⟩
        have h1 := hac e he
        have h2 : a⁻¹ * e * a⁻¹⁻¹ * e⁻¹ = a⁻¹ * (e * a * e⁻¹ * a⁻¹) * a⁻¹⁻¹ := by group
        have h3 : e * a * e⁻¹ * a⁻¹ = (a * e * a⁻¹ * e⁻¹)⁻¹ := by group
        have h4 : e * a * e⁻¹ * a⁻¹ ∈ Z := by rw [h3]; exact Z.inv_mem h1
        rw [h2, hconjZ a⁻¹ (Mc.inv_mem ha) _ h4]
        exact h4 }
  have hPD : P ≤ D := fun x hx => ⟨hPMc hx, fun e he => by
    have h1 := hEZ e he x hx
    have h2 : x * e * x⁻¹ * e⁻¹ = (e * x * e⁻¹ * x⁻¹)⁻¹ := by group
    rw [h2]; exact Z.inv_mem h1⟩
  have hDMc : D ≤ Mc := fun y hy => hy.1
  have hMcD : Mc ≤ Subgroup.normalizer (D : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun g hg y hy => ?_
    refine ⟨Mc.mul_mem (Mc.mul_mem hg hy.1) (Mc.inv_mem hg), fun e he => ?_⟩
    have he'' : g⁻¹ * e * g ∈ E := by
      have := hMcE g⁻¹ (Mc.inv_mem hg) e he
      simpa using this
    have h1 := hy.2 _ he''
    have h2 : (g * y * g⁻¹) * e * (g * y * g⁻¹)⁻¹ * e⁻¹ =
        g * (y * (g⁻¹ * e * g) * y⁻¹ * (g⁻¹ * e * g)⁻¹) * g⁻¹ := by group
    rw [h2, hconjZ g hg _ h1]
    exact h1
  have hD2 : IsPGroup 2 D := by
    intro y
    obtain ⟨y, hy⟩ := y
    have hy2N : y * y ∈ N := by
      refine ⟨Mc.mul_mem hy.1 hy.1, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
      have hζ := hy.2 e he
      obtain ⟨ζ, hζdef⟩ : ∃ ζ : G, ζ = y * e * y⁻¹ * e⁻¹ := ⟨_, rfl⟩
      rw [← hζdef] at hζ
      have hζ2 : ζ * ζ = 1 := by
        rcases hZ ζ hζ with h | h
        · rw [h]; simp
        · rw [h]; simpa [sq] using hz2
      have hyζ : y * ζ = ζ * y := mem_Mc_comm hζ hy.1
      have hye : y * e * y⁻¹ = ζ * e := by rw [hζdef]; group
      calc e * (y * y) = (y * y) * e := by
            have : (y * y) * e * (y * y)⁻¹ = e := by
              calc (y * y) * e * (y * y)⁻¹ = y * (y * e * y⁻¹) * y⁻¹ := by group
                _ = y * (ζ * e) * y⁻¹ := by rw [hye]
                _ = (y * ζ) * e * y⁻¹ := by group
                _ = (ζ * y) * e * y⁻¹ := by rw [hyζ]
                _ = ζ * (y * e * y⁻¹) := by group
                _ = ζ * (ζ * e) := by rw [hye]
                _ = (ζ * ζ) * e := by group
                _ = e := by rw [hζ2]; group
            calc e * (y * y) = ((y * y) * e * (y * y)⁻¹) * (y * y) := by rw [this]
              _ = (y * y) * e := by group
        _ = (y * y) * e := rfl
    obtain ⟨k, hk⟩ := hQ2 ⟨y * y, hNQ hy2N⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (y * y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hyy : y ^ 2 ^ (k + 1) = (y * y) ^ 2 ^ k := by rw [pow_succ', pow_mul, sq]
    show y ^ 2 ^ (k + 1) = 1
    rw [hyy]
    exact hk'
  have hDQ : D ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDMc hMcD hD2
  have hQeq : Q = P := le_antisymm hQP (hPD.trans hDQ)
  have hMcP : Mc ≤ Subgroup.normalizer (P : Set G) := hQeq ▸ hMcQ
  have hMcF : Mc ≤ Subgroup.normalizer (F : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun g hg x hx => ?_
    rw [hFmem]
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hMcP hg) x).mp (hFP hx), fun e he => ?_⟩
    have he'' : g⁻¹ * e * g ∈ E := by
      have := hMcE g⁻¹ (Mc.inv_mem hg) e he
      simpa using this
    have h1 := hFE' x hx _ he''
    calc (g * x * g⁻¹) * e = g * (x * (g⁻¹ * e * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * e * g) * x) * g⁻¹ := by rw [h1]
      _ = e * (g * x * g⁻¹) := by group
  have hPF' : P ≤ Subgroup.normalizer (F : Set G) := hPMc.trans hMcF
  have hFN : (F.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPF'
  let V := ↥P ⧸ F.subgroupOf P
  let ρ : ↥Mc →* MulAut V := quotAction hMcP hMcF
  have hρmk : ∀ (g : ↥Mc) (x : ↥P), ρ g (QuotientGroup.mk x) =
      QuotientGroup.mk (⟨(g : G) * x * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hMcP g.2) x).mp x.2⟩ : ↥P) :=
    fun g x => quotAction_mk hMcP hMcF g x
  have hVcard : Nat.card V = 16 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (F.subgroupOf P)
    have h2 : Nat.card (F.subgroupOf P) = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFP).toEquiv
    have hpos : 0 < Nat.card F := Nat.card_pos
    have h3 : 16 * Nat.card F = Nat.card V * Nat.card F := by
      rw [← hPF16, h1, h2]
    exact (Nat.eq_of_mul_eq_mul_right hpos h3).symm
  have hnormF : ∀ x ∈ P, ∀ y : G, y ∈ F ↔ x * y * x⁻¹ ∈ F := fun x hx y =>
    Subgroup.mem_normalizer_iff.mp (hPF' hx) y
  have htriv_of : ∀ g : ↥Mc, ρ g = 1 → ∀ x ∈ P, (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ F := by
    intro g hg x hx
    have h := congrArg (fun a : MulAut V => a (QuotientGroup.mk (⟨x, hx⟩ : ↥P))) hg
    simp only [hρmk, MulAut.one_apply] at h
    have h1 := QuotientGroup.eq.mp h.symm
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : x⁻¹ * ((g : G) * x * (g : G)⁻¹) ∈ F := h1
    have h3 := (hnormF x hx _).mp h2
    have h4 : x * (x⁻¹ * ((g : G) * x * (g : G)⁻¹)) * x⁻¹ = (g : G) * x * (g : G)⁻¹ * x⁻¹ := by
      group
    rwa [h4] at h3
  have hK : ∀ g : ↥Mc, ρ g = 1 ↔ (g : G) ∈ P := by
    intro g
    constructor
    · intro hg
      set K : Subgroup G := ρ.ker.map Mc.subtype with hKdef
      have hKMc : K ≤ Mc := Subgroup.map_subtype_le _
      have hKnorm : Mc ≤ Subgroup.normalizer (K : Set G) := by
        refine le_normalizer_of_forall_conj_mem fun m hm k hk => ?_
        obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hk
        refine Subgroup.mem_map.mpr ⟨⟨m, hm⟩ * g' * ⟨m, hm⟩⁻¹, ?_, ?_⟩
        · exact (MonoidHom.normal_ker ρ).conj_mem g' hg' ⟨m, hm⟩
        · simp
      have hK2 : IsPGroup 2 K := by
        refine isPGroup_two_of_odd_eq_one fun k hk hodd => ?_
        obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hk
        have hcent := centralizes_of_trivial_on_quotient hP2 hEP hEF hFP hZ2 hZcen hEZ hFE' hCE hFE2
          (g := (g' : G)) hodd (hMcEn g'.2) (hMcF g'.2) (fun z hz => mem_Mc_comm hz g'.2)
          (htriv_of g' hg')
        have hmem : (g' : G) ∈ pCoreOf 2 Mc :=
          S.charTwo_Mc ⟨g'.2, Subgroup.mem_centralizer_iff.mpr fun x hx =>
            (hcent x (hQeq ▸ hx)).symm⟩
        exact eq_one_of_odd_of_mem_pCoreOf hmem hodd
      have := (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKMc hKnorm hK2)
        (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
      exact hQeq ▸ this
    · intro hgP
      refine MulEquiv.ext fun v => ?_
      induction v using QuotientGroup.induction_on with | H x => ?_
      rw [hρmk]
      show _ = (QuotientGroup.mk x : V)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hc := hPP ((x : G)⁻¹) (P.inv_mem x.2) (g : G) hgP
      have h1 : ((g : G) * x * (g : G)⁻¹)⁻¹ * x =
          ((x : G)⁻¹ * (g : G) * ((x : G)⁻¹)⁻¹ * (g : G)⁻¹)⁻¹ := by group
      show ((g : G) * x * (g : G)⁻¹)⁻¹ * x ∈ F
      rw [h1]
      exact F.inv_mem hc
  have hkerMc : ρ.ker = P.subgroupOf Mc := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hK g
  set ρH : ↥H →* MulAut V := ρ.comp (Subgroup.inclusion hHMc) with hρH
  have hkerH : ρH.ker = P.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hK (Subgroup.inclusion hHMc h)
  set A : Subgroup (MulAut V) := ρ.range with hA
  set B : Subgroup (MulAut V) := ρH.range with hB
  have hBA : B ≤ A := by
    rintro _ ⟨h, rfl⟩
    exact ⟨Subgroup.inclusion hHMc h, rfl⟩
  have hAcard : Nat.card A * Nat.card P = Nat.card Mc := by
    have h1 := Subgroup.card_mul_index ρ.ker
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card ρ.ker = Nat.card P := by
      rw [hkerMc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPMc).toEquiv
    rw [h2] at h1
    rw [← h1]; ring
  have hBcard : Nat.card B * Nat.card P = Nat.card H := by
    have h1 := Subgroup.card_mul_index ρH.ker
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card ρH.ker = Nat.card P := by
      rw [hkerH]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
    rw [h2] at h1
    rw [← h1]; ring
  have hodd : ¬ 2 ∣ B.relIndex A := by
    have hrelMc : Odd (H.relIndex Mc) := by
      obtain ⟨Pp, hPp⟩ := S.exists_sylow
      have hTK : ¬ 2 ∣ (T.subgroupOf Mc).index := by
        have h := not_dvd_index_subgroupOf_of_sylow Pp (hPp.le.trans S.T_le_Mc)
        rwa [hPp] at h
      exact odd_relIndex_of_le S.T_le_H hHMc hTK
    have h1 := card_eq_card_mul_relIndex hBA
    have h2 := card_eq_card_mul_relIndex hHMc
    have hBpos : 0 < Nat.card B := Nat.card_pos
    have hPpos : 0 < Nat.card P := Nat.card_pos
    have key : B.relIndex A = H.relIndex Mc := by
      have h3 : Nat.card B * Nat.card P * B.relIndex A =
          Nat.card B * Nat.card P * H.relIndex Mc := by
        calc Nat.card B * Nat.card P * B.relIndex A
            = (Nat.card B * B.relIndex A) * Nat.card P := by ring
          _ = Nat.card A * Nat.card P := by rw [← h1]
          _ = Nat.card Mc := hAcard
          _ = Nat.card H * H.relIndex Mc := h2
          _ = (Nat.card B * Nat.card P) * H.relIndex Mc := by rw [← hBcard]
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hBpos hPpos) h3
    rw [key]
    have := Nat.odd_iff.mp hrelMc
    omega
  have hkerH' : ρH.ker = CFSG.Open.pCore 2 ↥H := by
    rw [hkerH]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  let eB : oTwoQuot ↥H ≃* ↥B :=
    (QuotientGroup.quotientMulEquivOfEq hkerH'.symm).trans (QuotientGroup.quotientKerEquivRange ρH)
  have hBcards : Nat.card B = 10 ∨ Nat.card B = 20 := by
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · left
      rw [← Nat.card_congr eB.toEquiv, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
        DihedralGroup.card]
    · right
      rw [← Nat.card_congr eB.toEquiv, Nat.card_congr e.toEquiv]; exact hSz
  have hcyc : ∀ S' : Subgroup ↥B, IsPGroup 2 S' → IsCyclic S' := by
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hBc : Nat.card ↥B = 10 := by
        rw [← Nat.card_congr eB.toEquiv, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
          DihedralGroup.card]
      exact fun S' hS' => isCyclic_of_isPGroup_of_card_ten hBc S' hS'
    · have hBc : Nat.card ↥B = 20 := by
        rw [← Nat.card_congr eB.toEquiv, Nat.card_congr e.toEquiv]; exact hSz
      obtain ⟨x, hx⟩ : ∃ x : ↥(Sz 0), orderOf x = 4 :=
        ⟨⟨szPsi.symm uS10, uS10_mem⟩, by
          rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, orderOf_uS10]⟩
      let eY : ↥(Sz 0) ≃* ↥B := e.symm.trans eB
      exact fun S' hS' => isCyclic_of_isPGroup_of_card_twenty hBc
        ⟨eY x, by rw [MulEquiv.orderOf_eq]; exact hx⟩ S' hS'
  have hcMc : c ∈ Mc := hHMc hcH
  let cV : MulAut V := ρ ⟨c, hcMc⟩
  have hcVB : cV ∈ B := ⟨⟨c, hcH⟩, rfl⟩
  have hcV5 : cV ^ 5 = 1 := by
    show ρ ⟨c, hcMc⟩ ^ 5 = 1
    rw [← map_pow]
    have : (⟨c, hcMc⟩ : ↥Mc) ^ 5 = 1 := Subtype.ext (by simpa using hc5)
    rw [this, map_one]
  have hmk1 : ∀ x : ↥P, (QuotientGroup.mk x : V) = 1 ↔ (x : G) ∈ F := by
    intro x
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcVfpf : ∀ v : V, cV v = v → v = 1 := by
    intro v hv
    induction v using QuotientGroup.induction_on with | H x => ?_
    change ρ ⟨c, hcMc⟩ (QuotientGroup.mk x) = QuotientGroup.mk x at hv
    rw [hρmk] at hv
    have h1 := QuotientGroup.eq.mp hv.symm
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (x : G)⁻¹ * (c * x * c⁻¹) ∈ F := h1
    have h3 := (hnormF x x.2 _).mp h2
    have h4 : (x : G) * ((x : G)⁻¹ * (c * x * c⁻¹)) * (x : G)⁻¹ = c * x * c⁻¹ * (x : G)⁻¹ := by
      group
    rw [h4] at h3
    rw [hmk1]
    by_contra hxF
    exact hcfpf x x.2 hxF h3
  let I : Set V := {v | ∃ x : ↥P, (x : G) ∉ F ∧ (x : G) * x = 1 ∧ v = QuotientGroup.mk x}
  have hI1 : (1 : V) ∉ I := by
    rintro ⟨x, hxF, -, hx⟩
    exact hxF ((hmk1 x).mp hx.symm)
  have hIne : I.Nonempty := ⟨QuotientGroup.mk ⟨j₀, hj₀P⟩, ⟨j₀, hj₀P⟩, hj₀F, hj₀sq, rfl⟩
  have hIA : ∀ a ∈ A, ∀ v ∈ I, a v ∈ I := by
    rintro _ ⟨g, rfl⟩ v ⟨x, hxF, hxsq, rfl⟩
    refine ⟨⟨(g : G) * x * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hMcP g.2) x).mp x.2⟩,
      ?_, ?_, hρmk g x⟩
    · intro hF'
      have hgi : (g : G)⁻¹ ∈ Subgroup.normalizer (F : Set G) := Subgroup.inv_mem _ (hMcF g.2)
      have := (Subgroup.mem_normalizer_iff.mp hgi ((g : G) * x * (g : G)⁻¹)).mp hF'
      apply hxF
      simpa [mul_assoc] using this
    · show (g : G) * x * (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) = 1
      calc (g : G) * x * (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹)
          = (g : G) * ((x : G) * x) * (g : G)⁻¹ := by group
        _ = 1 := by rw [hxsq]; group
  have hIB : ∀ v ∈ I, ∀ w ∈ I, ∃ b ∈ B, b v = w := by
    rintro _ ⟨x, hxF, hxsq, rfl⟩ _ ⟨x', hxF', hxsq', rfl⟩
    obtain ⟨h, hhH, hh⟩ := htrans x x.2 hxF hxsq x' x'.2 hxF' hxsq'
    refine ⟨ρH ⟨h, hhH⟩, ⟨⟨h, hhH⟩, rfl⟩, ?_⟩
    show ρ ⟨h, hHMc hhH⟩ (QuotientGroup.mk x) = QuotientGroup.mk x'
    rw [hρmk]
    congr 1
    exact Subtype.ext hh
  have hB20 : Nat.card B ∣ 20 := by
    rcases hBcards with h | h
    · rw [h]; norm_num
    · rw [h]
  have hAB : A = B := endgame_tits hVcard hBA hodd hB20 hcyc hcVB hcV5 hcVfpf hI1 hIne hIA hIB
  refine le_antisymm hHMc fun g hg => ?_
  have hgA : ρ ⟨g, hg⟩ ∈ A := ⟨⟨g, hg⟩, rfl⟩
  rw [hAB] at hgA
  obtain ⟨h, hh⟩ := hgA
  have h1 : ρ ((⟨(h : G), hHMc h.2⟩ : ↥Mc)⁻¹ * ⟨g, hg⟩) = 1 := by
    rw [map_mul, map_inv]
    have : ρ ⟨(h : G), hHMc h.2⟩ = ρ ⟨g, hg⟩ := hh
    rw [this, inv_mul_cancel]
  have h2 : (h : G)⁻¹ * g ∈ P := (hK _).mp h1
  have h3 : g = (h : G) * ((h : G)⁻¹ * g) := by group
  rw [h3]
  exact H.mul_mem h.2 (hPH h2)


end Setting1422

end CFSG.Quasithin
