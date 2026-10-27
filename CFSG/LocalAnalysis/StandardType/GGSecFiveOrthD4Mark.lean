module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

open scoped commutatorElement

private theorem ct_d4b_commutator_zpowers_eq_bot
    {G : Type} [Group G] {K : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hcomm : commutator ↥K = ⊤)
    (hcent : ∀ k ∈ K, ∃ c ∈ Subgroup.center ↥K, (c : G) = k * x * k⁻¹ * x⁻¹) :
    ⁅K, Subgroup.zpowers x⁆ = ⊥ := by
  let βf : ↥K → ↥K := fun k => ⟨⁅(k : G), x⁆, by
    have h : ⁅(k : G), x⁆ = (k : G) * (x * (k : G) * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h]
    exact K.mul_mem k.2 (K.inv_mem ((Subgroup.mem_normalizer_iff.mp hxN (k : G)).mp k.2))⟩
  have hβfc : ∀ k : ↥K, βf k ∈ Subgroup.center ↥K := by
    intro k
    obtain ⟨c, hc, hceq⟩ := hcent (k : G) k.2
    have hk : βf k = c := Subtype.ext (by
      show ⁅(k : G), x⁆ = (c : G)
      rw [commutatorElement_def, hceq])
    rw [hk]; exact hc
  let β : ↥K →* ↥K :=
    { toFun := βf
      map_one' := by ext; simp [βf]
      map_mul' := by
        intro a b
        apply Subtype.ext
        change ⁅((a : G) * (b : G)), x⁆ = (βf a : G) * (βf b : G)
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hb := Subgroup.mem_center_iff.mp (hβfc b)
        have ha := Subgroup.mem_center_iff.mp (hβfc a)
        have hba : (a : G) * (βf b : G) = (βf b : G) * (a : G) := by
          have := congrArg (fun z : ↥K => (z : G)) (hb ⟨a, a.2⟩)
          simpa using this
        have hab : (βf a : G) * (βf b : G) = (βf b : G) * (βf a : G) := by
          have := congrArg (fun z : ↥K => (z : G)) (ha (βf b))
          simpa using this.symm
        calc
          (a : G) * (βf b : G) * (a : G)⁻¹ * (βf a : G)
              = (βf b : G) * (a : G) * (a : G)⁻¹ * (βf a : G) := by rw [hba]
          _ = (βf b : G) * (βf a : G) := by group
          _ = (βf a : G) * (βf b : G) := hab.symm }
  have hker : _root_.commutator ↥K ≤ β.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hβfc a) (βf b)).symm
  have hβ1 : ∀ k : ↥K, β k = 1 := by
    intro k
    have htop : β.ker = ⊤ := le_antisymm le_top (by rw [← hcomm]; exact hker)
    exact MonoidHom.mem_ker.mp (htop.symm ▸ Subgroup.mem_top k)
  have hxcent : ∀ k : ↥K, x * (k : G) * x⁻¹ = (k : G) := by
    intro k
    have hcast : ⁅(k : G), x⁆ = 1 := by
      change (β k : G) = 1
      exact congrArg Subtype.val (hβ1 k)
    have hmul : (k : G) * x = x * (k : G) := commutatorElement_eq_one_iff_mul_comm.mp hcast
    calc x * (k : G) * x⁻¹ = (k : G) * x * x⁻¹ := by rw [← hmul]
      _ = (k : G) := by group
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hxk : Commute x (k : G) := by
    rw [commute_iff_eq]
    calc x * (k : G) = x * (k : G) * x⁻¹ * x := by group
      _ = (k : G) * x := by rw [hxcent ⟨k, hk⟩]
  exact (commute_iff_eq (x ^ n) (k : G)).mp (hxk.zpow_left n)

theorem ggOrthD4_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hRQ : GGReflRealizedQFourNbrInput) {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    {s : MulAut ↥Bs} (hs : s ∈ ggAutomizer K Bs) (hsr : GGIsReflection 3 s) (hunreal : ¬ GGRealized 3 Bs s) :
    orderOf x = 3 ∧ x ∈ Subgroup.normalizer (K : Set G) ∧
      (¬ ∀ k ∈ K, ∃ c ∈ Subgroup.center ↥K, (c : G) = k * x * k⁻¹ * x⁻¹) ∧
      LargeEvenMarking K (fun lab _ _ I _ θ => lab.n = 1 ∧
        ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = x⁻¹ * l * x) φ) := by
  obtain ⟨hp, habel, hxBs, -, -⟩ := (S.cfg.1.1).tableB_facts
  have hx3 : x ^ 3 = 1 := habel.2 x hxBs
  have hx1 : x ≠ 1 := (S.cfg.1.1).1.2.2.2.2.2.2.1.2.2.1
  have hxord : orderOf x = 3 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (n := 3) (by norm_num) hx3 ?_
    intro p hpp hpdvd
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp hpdvd
    rw [hp3]
    simpa using hx1
  obtain ⟨hperf, lab, hlab, hraw⟩ := S.cfg.1.2.2.1.2 y K hnb
  obtain ⟨-, -, -, -, -, -, -, hBsN, -⟩ := largeEvenRawDatum_exists hraw
  have hxNK : x ∈ Subgroup.normalizer (K : Set G) := hBsN hxBs
  have hlabn : lab.n = 1 := by
    by_contra hne1
    have h2 : 2 ≤ lab.n := by
      have h1 : 1 ≤ lab.n := hlab.1
      omega
    have hq4 : GGLabQFour 3 lab := h2
    have hKq : GGInnerDiagOnLabel GGLabQFour 3 Bs K := by
      refine ⟨hperf, lab, hlab, ?_⟩
      refine largeEvenRawDatum_mono ?_ hraw
      rintro R' _ I' F' ⟨hsR', hna', θ', hBsN', hInd'⟩
      exact ⟨hsR', hna', θ', hq4, hBsN', hInd'⟩
    have hR := hRQ G B Bs x L D J 𝒦 S.cfg S.split y K hnb hKq
    have hyBs : y ∈ Bs := S.cfg.1.1.2.1.1 hnb.1.2.1
    have hKpc : LargeEvenPComponent 3 (Subgroup.centralizer ({y} : Set G)) K := hnb.1.2.2.2.2.1
    have hX : CFSG.Open.GLAPComponent 3 (Subgroup.centralizer ({y} : Set G)) K :=
      (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 3 _ K).mp hKpc
    exact hunreal (ggRealized_of_reflRealizedIn (p := 3) hp hyBs hX hR hs hsr)
  refine ⟨hxord, hxNK, ?_, ?_⟩
  · intro hcent
    have hbot := ct_d4b_commutator_zpowers_eq_bot hxNK hperf hcent
    exact hnb.2.2.2 (hbot.symm ▸ bot_le)
  · refine ⟨hperf, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R' _ I' F' ⟨hsR', hna', θ', hBsN', hInd'⟩
    exact ⟨hsR', hna', θ', hlabn, hInd' x hxBs⟩

end CFSG.StandardType.OrthF3

end
