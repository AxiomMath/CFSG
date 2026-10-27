module

public import CFSG.Quasithin.EmptyFaithful.ModHEl
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12
public import CFSG.Quasithin.EmptyFaithful.ModHPerm

public section

namespace CFSG.Quasithin.ModH.S12

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Quasithin.R3c14 CFSG.Quasithin.ModG

abbrev G : Type := ↥NativeSporadic.M12

@[expose] def cd (x : G) : ℕ := pkn 12 x.1

theorem cd_mul (x y : G) : cd (x * y) = compn 12 (cd x) (cd y) := by
  simp only [cd, Subgroup.coe_mul]
  exact pkn_mul (by norm_num) _ _

theorem cd_one : cd 1 = kIdn 12 := by
  simp only [cd, OneMemClass.coe_one]
  exact pkn_one 12

theorem cd_injective : Function.Injective cd :=
  fun x y h => Subtype.ext (pkn_injective (by norm_num) h)

@[expose] def alph : List G := [m12a, m12b, m12a⁻¹, m12b⁻¹]

@[expose] def aC : List ℕ := [221918013177243716, 402193972887359592, 221918013177243716, 193874731646158985]

@[expose] def gW : List (List ℕ) :=
  [[3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3],
    [3, 2, 3, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1],
    [3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 1, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3]]

@[expose] def tg : List G := gW.map (ev alph)

@[expose] def gC : List ℕ := [435871914113969217, 263850024634551585, 433657392340932682]

@[expose] def tW : List (List ℕ) :=
  [[],
    [0],
    [1],
    [2],
    [0, 1],
    [0, 2],
    [1, 0],
    [1, 2],
    [2, 0],
    [2, 1],
    [2, 2],
    [0, 1, 0],
    [0, 1, 2],
    [0, 2, 0],
    [0, 2, 1],
    [0, 2, 2],
    [1, 0, 1],
    [1, 0, 2],
    [1, 2, 0],
    [1, 2, 1],
    [1, 2, 2],
    [2, 0, 1],
    [2, 0, 2],
    [2, 1, 0],
    [0, 1, 0, 1],
    [0, 1, 0, 2],
    [0, 1, 2, 0],
    [0, 1, 2, 1],
    [0, 1, 2, 2],
    [0, 2, 0, 1],
    [0, 2, 0, 2],
    [0, 2, 1, 0],
    [1, 0, 1, 2],
    [1, 0, 2, 1],
    [1, 0, 2, 2],
    [1, 2, 0, 1],
    [1, 2, 0, 2],
    [1, 2, 1, 0],
    [2, 0, 1, 2],
    [2, 0, 2, 0],
    [2, 0, 2, 1],
    [2, 1, 0, 1],
    [2, 1, 0, 2],
    [0, 1, 0, 1, 2],
    [0, 1, 0, 2, 1],
    [0, 1, 0, 2, 2],
    [0, 1, 2, 0, 1],
    [0, 1, 2, 0, 2],
    [0, 1, 2, 1, 0],
    [0, 2, 0, 1, 2],
    [0, 2, 0, 2, 0],
    [0, 2, 0, 2, 1],
    [0, 2, 1, 0, 1],
    [0, 2, 1, 0, 2],
    [1, 0, 1, 2, 1],
    [1, 0, 1, 2, 2],
    [1, 2, 0, 1, 2],
    [1, 2, 0, 2, 1],
    [1, 2, 1, 0, 1],
    [0, 1, 0, 1, 2, 1],
    [0, 1, 0, 1, 2, 2],
    [0, 1, 2, 0, 1, 2],
    [0, 1, 2, 0, 2, 1],
    [0, 1, 2, 1, 0, 1]]

@[expose] def tK : List ℕ :=
  [445092485129178177, 435871914113969217, 263850024634551585, 433657392340932682, 328870812907285729, 433655470535942212, 255733487713495329, 253505716032315691, 439390282441720906, 257868612498626858, 444001700937830469, 337009318586061025, 325563585143249123, 441574116805477444, 329926412954968292, 436962698296928325, 76676856334887297, 253516941156948260, 261433218457306411, 438020288805019723, 264940808817447205, 333479793791239402, 443999332167978056, 259251753062536490, 83711602528981377, 325574328776335594, 331309587846300899, 438018298349885507, 327780028716001509, 259241043754648868, 436964654628285510, 333491053240816868, 73369662896939395, 77732559361153412, 256824134591655205, 79104474800620939, 264951552651955494, 441571679183869003, 335907446776238310, 435874076396202056, 336998299613662440, 81285940197234058, 263860974419808552, 73367259600656779, 77730087414473098, 335918671699512549, 81283984067298691, 327790841200717032, 439392720063075395, 256812978318715176, 445090185009532998, 255722400090762534, 79102518670431620, 328881694042335462, 257879837623132451, 75586209448275333, 84804274388832648, 83713696160943494, 331298397046740203, 329937156588181739, 84802249407204741, 75583772028152198, 76674624865512840, 261422440498894115]

@[expose] def zC : ℕ := 444001700937830469

theorem alph_codes : alph.map cd = aC := by decide +kernel

theorem tg_codes : tg.map cd = gC := by
  rw [tg, map_c_evg cd (compn 12) (kIdn 12) cd_mul cd_one, alph_codes]
  decide +kernel

theorem tK_eq : tW.map (evcg (compn 12) (kIdn 12) gC) = tK := by decide +kernel

theorem dataOK_true : dataOK (compn 12) (kIdn 12) gC tK (buckets tK 0) 0 zC = true := by decide +kernel

theorem tK_length : tK.length = 64 := by decide +kernel

theorem centerSmall : CenterSmall G := by
  refine centerSmall_of_dataOK cd (compn 12) (kIdn 12) cd_mul cd_one cd_injective tg tW tK gC zC tg_codes tK_eq 0 (buckets tK 0) rfl
    dataOK_true 6 1485 (by rw [tK_length]; norm_num) ?_ (by norm_num)
  rw [tK_length]
  have := m12_card
  rw [show Nat.card G = Nat.card NativeSporadic.M12 from rfl, this]

theorem not_elConfig :
    ¬ ElConfig (CFSG.Blueprint.NativeSporadic.Carrier .M12) := by
  have h : ¬ ElConfig G := not_elConfig_of_center (m12_sylow_pointwise_inner) centerSmall
  exact h

end CFSG.Quasithin.ModH.S12
